//! Probing based inprocessing (Kissat `probe.c`): equivalent literal
//! substitution (`substitute.c`), failed literal probing (in the spirit of
//! `backbone.c`) and clause vivification (`vivify.c`).

use crate::arena::{CRef, INVALID_REF};
use crate::simplify::Simplified;
use crate::solver::{Conflict, Solver, ANALYZED, BINARY, DECISION_REASON, ELIMINATED};
use crate::stats::nlogpown;
use crate::types::{Lit, Var};
use crate::watch::{self, Watch};

impl Solver {
    pub fn probing_due(&self) -> bool {
        self.opts.simplify
            && self.opts.probe
            && self.last_reduce_conflicts != self.stats.conflicts
            && self.limits.probe_conflicts < self.stats.conflicts
    }

    pub fn probe(&mut self) -> bool {
        let start = std::time::Instant::now();
        let res = self.probe_untimed();
        self.stats.time_probe += start.elapsed().as_secs_f64();
        res
    }

    /// Run all probing based simplifications.  Returns false if the formula
    /// became unsatisfiable.
    fn probe_untimed(&mut self) -> bool {
        self.stats.probings += 1;
        if self.backtrack_propagate_root() {
            self.probing = true;
            let ok = self.resync_watches()
                && self.congruence()
                && (!self.opts.substitute || self.substitute())
                && self.failed_literals()
                && (!self.opts.vivify || self.vivify())
                && self.sweep()
                && (!self.opts.substitute || self.substitute())
                && self.transitive_reduction()
                && self.factor();
            self.probing = false;
            let _ = ok;
        }
        let delta = self.opts.probeint as f64 * nlogpown(self.stats.probings, 1);
        self.limits.probe_conflicts = self.stats.conflicts + self.scale_delta(delta as u64);
        self.last_probe_ticks = self.stats.search_ticks;
        self.recount_phase_heights();
        self.report('p');
        !self.inconsistent
    }

    /// Initial preprocessing before search (Kissat `preprocess.c`).
    pub fn preprocess(&mut self) -> bool {
        if !self.opts.preprocess || !self.opts.simplify || !self.opts.probe {
            return true;
        }
        if !self.backtrack_propagate_root() {
            return false;
        }
        self.probing = true;
        let ok = self.resync_watches()
            && self.congruence()
            && self.sweep()
            && (!self.opts.substitute || self.substitute())
            && self.factor();
        self.probing = false;
        let _ = ok;
        self.report('P');
        !self.inconsistent
    }

    /// At the root: simplify all clauses, collect the arena and watch all
    /// clauses again.  Returns false on inconsistency.
    pub fn resync_watches(&mut self) -> bool {
        debug_assert_eq!(self.level, 0);
        let mut c = 0;
        while (c as usize) < self.arena.len() && !self.inconsistent {
            let next = self.arena.next(c);
            if !self.arena.garbage(c) {
                self.simplify_clause_at_root(c);
            }
            c = next;
        }
        self.fixed_at_last_collect = self.stats.units;
        self.collect(0, true);
        self.flush_pending_units();
        if !self.inconsistent && self.propagate().is_some() {
            self.mark_inconsistent();
        }
        !self.inconsistent
    }

    // ------------------------------------------------------------------
    // Equivalent literal substitution.

    /// Successors of `lit` in the binary implication graph.
    fn implied_by_binaries(&self, lit: Lit, out: &mut Vec<Lit>) {
        out.clear();
        for w in watch::iter(&self.watches[(!lit).idx()]) {
            if let Watch::Binary(other) = w {
                if self.value(other) == 0 {
                    out.push(other);
                }
            }
        }
    }

    /// Compute strongly connected components of the binary implication graph
    /// (iterative Tarjan) and return a representative for every literal.
    fn equivalence_classes(&mut self) -> Option<Vec<Lit>> {
        let n = 2 * self.vars;
        let mut repr: Vec<Lit> = (0..n as u32).map(Lit).collect();
        let mut index = vec![u32::MAX; n];
        let mut low = vec![0u32; n];
        let mut on_stack = vec![false; n];
        let mut scc_stack: Vec<Lit> = Vec::new();
        let mut counter = 0u32;
        let mut succ: Vec<Lit> = Vec::new();
        // DFS stack of (literal, successors, next successor position).
        let mut dfs: Vec<(Lit, Vec<Lit>, usize)> = Vec::new();
        let mut found = false;
        for root in 0..n as u32 {
            let root = Lit(root);
            if index[root.idx()] != u32::MAX || self.value(root) != 0 {
                continue;
            }
            if self.flags[root.vidx()] & ELIMINATED != 0 {
                continue;
            }
            self.implied_by_binaries(root, &mut succ);
            index[root.idx()] = counter;
            low[root.idx()] = counter;
            counter += 1;
            scc_stack.push(root);
            on_stack[root.idx()] = true;
            dfs.push((root, succ.clone(), 0));
            while let Some((lit, succs, pos)) = dfs.last_mut() {
                let lit = *lit;
                if *pos < succs.len() {
                    let next = succs[*pos];
                    *pos += 1;
                    if index[next.idx()] == u32::MAX {
                        self.implied_by_binaries(next, &mut succ);
                        index[next.idx()] = counter;
                        low[next.idx()] = counter;
                        counter += 1;
                        scc_stack.push(next);
                        on_stack[next.idx()] = true;
                        dfs.push((next, succ.clone(), 0));
                    } else if on_stack[next.idx()] {
                        low[lit.idx()] = low[lit.idx()].min(index[next.idx()]);
                    }
                    continue;
                }
                dfs.pop();
                if let Some((parent, _, _)) = dfs.last() {
                    let p = parent.idx();
                    low[p] = low[p].min(low[lit.idx()]);
                }
                if low[lit.idx()] != index[lit.idx()] {
                    continue;
                }
                // Pop the component; the representative is the literal with
                // the smallest variable index.
                let start = scc_stack.iter().rposition(|&l| l == lit).unwrap();
                let component: Vec<Lit> = scc_stack.drain(start..).collect();
                let mut best = component[0];
                for &l in &component {
                    on_stack[l.idx()] = false;
                    if l.var() < best.var() {
                        best = l;
                    }
                }
                if component.len() > 1 {
                    for &l in &component {
                        if l == !best {
                            // Both polarities equivalent: unsatisfiable.
                            if let Some(p) = self.proof.as_mut() {
                                p.add(&[l]);
                                p.add(&[!l]);
                            }
                            self.mark_inconsistent();
                            return None;
                        }
                        repr[l.idx()] = best;
                        found = true;
                    }
                }
            }
        }
        if !found {
            return Some(Vec::new());
        }
        // Components of complementary literals are complementary, but the
        // representatives are chosen independently: normalize.
        for v in 0..self.vars as u32 {
            let pos = Lit::new(v, false);
            let r = repr[pos.idx()];
            repr[(!pos).idx()] = !r;
        }
        Some(repr)
    }

    /// Substitute equivalent literals.  Returns false on inconsistency.
    pub fn substitute(&mut self) -> bool {
        debug_assert_eq!(self.level, 0);
        let Some(repr) = self.equivalence_classes() else {
            return false;
        };
        if repr.is_empty() {
            return true;
        }
        let mut substituted: Vec<Var> = Vec::new();
        for v in 0..self.vars as Var {
            let pos = Lit::new(v, false);
            if repr[pos.idx()] != pos {
                substituted.push(v);
            }
        }
        if substituted.is_empty() {
            return true;
        }
        let mut deletions: Vec<Vec<Lit>> = Vec::new();
        // Rewrite binary clauses.
        let mut binaries: Vec<(Lit, Lit)> = Vec::new();
        for idx in 0..self.watches.len() {
            let lit = Lit(idx as u32);
            for w in watch::iter(&self.watches[idx]) {
                if let Watch::Binary(other) = w {
                    if lit < other {
                        binaries.push((lit, other));
                    }
                }
            }
        }
        for ws in &mut self.watches {
            let mut j = 0;
            let mut i = 0;
            while i < ws.len() {
                if watch::is_binary(ws[i]) {
                    i += 1;
                } else {
                    ws[j] = ws[i];
                    ws[j + 1] = ws[i + 1];
                    i += 2;
                    j += 2;
                }
            }
            ws.truncate(j);
        }
        self.stats.clauses_binary = 0;
        let mut new_binaries: Vec<(Lit, Lit)> = Vec::new();
        for &(a, b) in &binaries {
            let (ra, rb) = (repr[a.idx()], repr[b.idx()]);
            if ra == a && rb == b {
                new_binaries.push((a, b));
                continue;
            }
            deletions.push(vec![a, b]);
            if ra == !rb {
                continue;
            }
            if ra == rb {
                if let Some(p) = self.proof.as_mut() {
                    p.add(&[ra]);
                }
                match self.value(ra) {
                    0 => self.assign_unit(ra),
                    v if v < 0 => {
                        self.mark_inconsistent();
                        return false;
                    }
                    _ => {}
                }
                continue;
            }
            let (x, y) = if ra < rb { (ra, rb) } else { (rb, ra) };
            if let Some(p) = self.proof.as_mut() {
                p.add(&[x, y]);
            }
            new_binaries.push((x, y));
        }
        new_binaries.sort_unstable();
        new_binaries.dedup();
        for &(a, b) in &new_binaries {
            self.new_binary(a, b);
        }
        // Rewrite large clauses.
        let mut lits: Vec<Lit> = Vec::new();
        let mut c = 0;
        while (c as usize) < self.arena.len() {
            let next = self.arena.next(c);
            if !self.arena.garbage(c)
                && self.arena.lits(c).iter().any(|l| repr[l.idx()] != *l)
            {
                lits.clear();
                let mut tautology = false;
                for &l in self.arena.lits(c) {
                    let r = repr[l.idx()];
                    if self.marks[r.idx()] != 0 {
                        continue;
                    }
                    if self.marks[(!r).idx()] != 0 {
                        tautology = true;
                        break;
                    }
                    self.marks[r.idx()] = 1;
                    lits.push(r);
                }
                for &l in &lits {
                    self.marks[l.idx()] = 0;
                }
                if tautology {
                    self.mark_garbage(c);
                } else {
                    self.rewrite_clause(c, &lits, &mut deletions);
                    if self.inconsistent {
                        return false;
                    }
                }
            }
            c = next;
        }
        // Extension stack and variable status.
        for &v in &substituted {
            let l = Lit::new(v, false);
            let r = repr[l.idx()];
            self.push_extension(l, &[l, !r]);
            self.push_extension(!l, &[!l, r]);
            self.flags[v as usize] |= ELIMINATED;
            self.eliminated += 1;
            self.unassigned -= 1;
            self.queue.dequeue(v);
            // Keep the representative a candidate for elimination.
            self.mark_removed_var(r.vidx());
        }
        self.stats.substituted += substituted.len() as u64;
        if let Some(p) = self.proof.as_mut() {
            for d in &deletions {
                p.delete(d);
            }
        }
        self.resync_watches()
    }

    /// Replace the literals of clause `c` by `lits` (with proof lines; the
    /// deletion of the old clause is deferred to `deletions`).
    fn rewrite_clause(&mut self, c: CRef, lits: &[Lit], deletions: &mut Vec<Vec<Lit>>) {
        if let Some(p) = self.proof.as_mut() {
            p.add(lits);
        }
        deletions.push(self.arena.lits(c).to_vec());
        let redundant = self.arena.redundant(c);
        match lits.len() {
            0 => self.mark_inconsistent(),
            1 => {
                let v = self.value(lits[0]);
                if v == 0 {
                    self.assign_unit(lits[0]);
                } else if v < 0 {
                    self.mark_inconsistent();
                }
            }
            2 => self.new_binary(lits[0], lits[1]),
            _ => {
                let size = lits.len();
                self.arena.lits_mut(c)[..size].copy_from_slice(lits);
                self.arena.shrink(c, size);
                return;
            }
        }
        // Removed: account like garbage but without a proof deletion (the
        // deletion is emitted later).
        if redundant {
            self.stats.clauses_redundant -= 1;
        } else {
            self.stats.clauses_irredundant -= 1;
        }
        self.arena.set_garbage(c, true);
    }

    // ------------------------------------------------------------------
    // Failed literal probing.

    fn failed_literals(&mut self) -> bool {
        debug_assert_eq!(self.level, 0);
        let limit = self.stats.probing_ticks
            + self.effort_limit_from(self.last_probe_ticks, self.opts.probeeffort);
        // Probe roots of the binary implication graph: literals which imply
        // something but are not implied by a binary clause.
        let mut candidates: Vec<Lit> = Vec::new();
        for idx in 0..2 * self.vars {
            let lit = Lit(idx as u32);
            if self.value(lit) != 0 || self.flags[lit.vidx()] & ELIMINATED != 0 {
                continue;
            }
            let has_binary = |l: Lit| watch::iter(&self.watches[l.idx()]).any(|w| matches!(w, Watch::Binary(_)));
            if has_binary(!lit) && !has_binary(lit) {
                candidates.push(lit);
            }
        }
        for lit in candidates {
            if self.stats.probing_ticks > limit || self.terminated() {
                break;
            }
            if self.value(lit) != 0 {
                continue;
            }
            self.assign_decision(lit);
            let conflict = self.propagate();
            self.backtrack_without_updating_phases(0);
            if conflict.is_some() {
                self.stats.failed += 1;
                self.learned_unit(!lit);
                if self.propagate().is_some() {
                    self.mark_inconsistent();
                    return false;
                }
            }
        }
        true
    }

    pub fn effort_limit_from(&self, last_ticks: u64, effort: u64) -> u64 {
        let reference = self.stats.search_ticks - last_ticks;
        let reference = reference.max(1_000_000 * self.opts.mineffort);
        (reference as f64 * effort as f64 * 1e-3) as u64
    }

    // ------------------------------------------------------------------
    // Vivification.

    fn vivify(&mut self) -> bool {
        let start = std::time::Instant::now();
        let res = self.vivify_untimed();
        self.stats.time_vivify += start.elapsed().as_secs_f64();
        res
    }

    fn vivify_untimed(&mut self) -> bool {
        debug_assert_eq!(self.level, 0);
        let total = self.effort_limit_from(self.last_probe_ticks, self.opts.vivifyeffort);
        let tier1 = self.tier1_limit();
        let tier2 = self.tier2_limit();
        // tier1, tier2, tier3 redundant, irredundant.
        let shares = [
            self.opts.vivifytier1,
            self.opts.vivifytier2,
            self.opts.vivifytier3,
            self.opts.vivifyirr,
        ];
        let sum: u64 = shares.iter().sum::<u64>().max(1);
        let irr_delayed = self.delay_vivifyirr.delaying();
        for (tier, share) in shares.iter().enumerate() {
            if *share == 0 || (tier == 3 && irr_delayed) {
                continue;
            }
            let (vivified_before, checks_before) = (self.stats.vivified, self.stats.vivify_checks);
            let mut candidates: Vec<CRef> = Vec::new();
            let mut c = 0;
            while (c as usize) < self.arena.len() {
                let next = self.arena.next(c);
                if !self.arena.garbage(c) {
                    let red = self.arena.redundant(c);
                    let glue = self.arena.glue(c);
                    let t = if !red {
                        3
                    } else if glue <= tier1 {
                        0
                    } else if glue <= tier2 {
                        1
                    } else {
                        2
                    };
                    if t == tier {
                        candidates.push(c);
                    }
                }
                c = next;
            }
            let limit = self.stats.probing_ticks + total * share / sum;
            if !self.vivify_clauses(candidates, limit) {
                return false;
            }
            if tier == 3 {
                let tried = (self.stats.vivify_checks - checks_before).max(1);
                if ((self.stats.vivified - vivified_before) as f64) / (tried as f64) < 0.01 {
                    self.delay_vivifyirr.bump();
                } else {
                    self.delay_vivifyirr.reduce();
                }
            }
        }
        true
    }

    fn vivify_clauses(&mut self, mut candidates: Vec<CRef>, limit: u64) -> bool {
        if candidates.is_empty() {
            return true;
        }
        // Count literal occurrences in candidates; literals are tried in
        // order of decreasing occurrence, clauses sorted lexicographically by
        // that order so decisions can be reused.
        let mut count = vec![0u32; 2 * self.vars];
        for &c in &candidates {
            for &l in self.arena.lits(c) {
                count[l.idx()] += 1;
            }
        }
        // Prefer clauses not tried before.
        let mut sorted: Vec<(bool, Vec<Lit>, CRef)> = candidates
            .drain(..)
            .map(|c| {
                let mut lits = self.arena.lits(c).to_vec();
                lits.sort_unstable_by(|a, b| count[b.idx()].cmp(&count[a.idx()]).then(a.cmp(b)));
                (self.arena.vivify(c), lits, c)
            })
            .collect();
        sorted.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.cmp(&b.1)));
        let mut tried_all = true;
        for (_, lits, c) in sorted {
            if self.stats.probing_ticks > limit || self.terminated() {
                tried_all = false;
                break;
            }
            if self.arena.garbage(c) || self.arena.lits(c).len() != lits.len() {
                continue;
            }
            self.arena.set_vivify(c, true);
            self.stats.vivify_checks += 1;
            if !self.vivify_clause(c, &lits) {
                return false;
            }
        }
        if tried_all {
            // Everything was tried: start over next time.
            let mut c = 0;
            while (c as usize) < self.arena.len() {
                let next = self.arena.next(c);
                self.arena.set_vivify(c, false);
                c = next;
            }
        }
        if self.level > 0 {
            self.backtrack_without_updating_phases(0);
        }
        true
    }

    fn vivify_clause(&mut self, c: CRef, lits: &[Lit]) -> bool {
        // Root-satisfied clauses are removed.
        if lits.iter().any(|&l| self.fixed(l) > 0) {
            if self.level > 0 {
                self.backtrack_without_updating_phases(0);
            }
            if !self.is_reason(c) {
                self.mark_garbage(c);
            }
            return true;
        }
        // Reuse decisions which match the negation of the literal order.
        let mut keep = 0;
        {
            let mut k = 0;
            while (keep as usize) < self.level as usize && k < lits.len() {
                let l = lits[k];
                if self.fixed(l) != 0 {
                    k += 1;
                    continue;
                }
                if self.frames[keep as usize + 1].decision != !l {
                    break;
                }
                keep += 1;
                k += 1;
            }
        }
        if keep < self.level {
            self.backtrack_without_updating_phases(keep);
        }
        for &l in lits {
            self.marks[l.idx()] = 1;
        }
        self.ignore = c;
        let mut conflict: Option<Conflict> = None;
        let mut implied = Lit::INVALID;
        'assume: for &l in lits {
            let v = self.value(l);
            if v > 0 {
                implied = l;
                break;
            }
            if v < 0 {
                continue;
            }
            self.assign_decision(!l);
            let start = self.propagated;
            if let Some(cf) = self.propagate() {
                conflict = Some(cf);
                break;
            }
            // A literal of the clause became true: it is implied.
            for &t in &self.trail[start..] {
                if self.marks[t.idx()] > 0 {
                    implied = t;
                    break 'assume;
                }
            }
        }
        self.ignore = INVALID_REF;
        for &l in lits {
            self.marks[l.idx()] = 0;
        }
        if implied != Lit::INVALID {
            // Prefer the implied literal earliest on the trail.
            let mut best_trail = u32::MAX;
            for &l in lits {
                if self.value(l) > 0 && self.assigned[l.vidx()].trail < best_trail {
                    best_trail = self.assigned[l.vidx()].trail;
                    implied = l;
                }
            }
        }
        // Collect the decisions involved.  Without conflict and implied
        // literal all literals are false and the clause itself is the
        // conflict.
        let mut seeds: Vec<Lit> = Vec::new();
        let mut used_redundant = false;
        match conflict {
            Some(Conflict::Binary(a, b)) => seeds.extend([a, b]),
            Some(Conflict::Large(d)) => {
                used_redundant |= self.arena.redundant(d);
                seeds.extend_from_slice(self.arena.lits(d));
            }
            None if implied == Lit::INVALID => seeds.extend_from_slice(lits),
            None => {
                let a = self.assigned[implied.vidx()];
                if a.level == 0 {
                    // Satisfied at the root (by a new unit).
                } else if a.reason == DECISION_REASON {
                    seeds.push(!implied);
                } else if a.has(BINARY) {
                    seeds.push(Lit(a.reason));
                } else {
                    used_redundant |= self.arena.redundant(a.reason);
                    seeds.extend(self.arena.lits(a.reason).iter().filter(|&&x| x != implied));
                }
            }
        }
        let decisions = self.vivify_analyze(&seeds, &mut used_redundant);
        let mut new_lits: Vec<Lit> = decisions.iter().map(|&d| !d).collect();
        if implied != Lit::INVALID {
            new_lits.push(implied);
        }
        // Keep the clause order of the original.
        new_lits.sort_by_key(|l| lits.iter().position(|x| x == l));
        let original_size = self.arena.size(c);
        if self.is_reason(c) {
            return true;
        }
        if new_lits.len() < original_size {
            self.backtrack_without_updating_phases(0);
            self.stats.vivified += 1;
            self.unwatch_clause(c);
            if self.strengthen_to(c, &new_lits) == Simplified::Large {
                self.watch_clause(c);
            }
            if self.inconsistent {
                return false;
            }
            if self.propagate().is_some() {
                self.mark_inconsistent();
                return false;
            }
            return true;
        }
        let redundant = self.arena.redundant(c);
        let derived = conflict.is_some() || implied != Lit::INVALID;
        if (implied != Lit::INVALID && redundant) || (derived && !redundant && !used_redundant) {
            // The clause is implied by the other (irredundant) clauses.
            self.stats.vivified += 1;
            self.stats.vivify_removed += 1;
            self.mark_garbage(c);
        }
        true
    }

    /// Decisions on which the (false) seed literals depend.  Sets
    /// `used_redundant` if a redundant reason was involved.
    fn vivify_analyze(&mut self, seeds: &[Lit], used_redundant: &mut bool) -> Vec<Lit> {
        let mut stack: Vec<Lit> = Vec::new();
        let mut marked: Vec<Var> = Vec::new();
        let mut decisions: Vec<Lit> = Vec::new();
        for &s in seeds {
            stack.push(s);
        }
        while let Some(lit) = stack.pop() {
            let v = lit.var();
            let a = self.assigned[v as usize];
            if a.level == 0 || a.has(ANALYZED) {
                continue;
            }
            self.assigned[v as usize].flags |= ANALYZED;
            marked.push(v);
            if a.reason == DECISION_REASON {
                // The literal on the trail is the decision itself.
                let d = if self.value(lit) > 0 { lit } else { !lit };
                decisions.push(d);
            } else if a.has(BINARY) {
                stack.push(Lit(a.reason));
            } else {
                *used_redundant |= self.arena.redundant(a.reason);
                stack.extend_from_slice(self.arena.lits(a.reason));
            }
        }
        for v in marked {
            self.assigned[v as usize].flags &= !ANALYZED;
        }
        decisions
    }
}

impl Solver {
    /// Transitive reduction of the binary implication graph (Kissat
    /// `transitive.c`): a binary clause `(!a | b)` is removed if `b` is
    /// reachable from `a` without it.  Reaching `!a` makes `!a` a unit.
    pub fn transitive_reduction(&mut self) -> bool {
        debug_assert_eq!(self.level, 0);
        if !self.opts.transitive {
            return true;
        }
        let limit = self.stats.probing_ticks
            + self.effort_limit_from(self.last_probe_ticks, self.opts.transitiveeffort);
        let n = 2 * self.vars;
        let mut stamp = vec![0u32; n];
        let mut current = 0u32;
        let mut queue: Vec<Lit> = Vec::new();
        let mut removed = 0u64;
        let start = (self.stats.probings as usize * 7919) % n.max(1);
        for k in 0..n {
            if self.stats.probing_ticks > limit || self.inconsistent {
                break;
            }
            let src = Lit(((start + k) % n) as u32);
            if self.value(src) != 0 || self.flags[src.vidx()] & ELIMINATED != 0 {
                continue;
            }
            // Successors of `src`: binary clauses (!src | dst).
            let dsts: Vec<Lit> = watch::iter(&self.watches[(!src).idx()])
                .filter_map(|w| match w {
                    Watch::Binary(d) => Some(d),
                    _ => None,
                })
                .collect();
            for dst in dsts {
                if self.value(dst) != 0 || self.value(src) != 0 {
                    continue;
                }
                // Each clause once: (!src | dst) is also (!(!dst) | !src).
                if (!src) > dst {
                    continue;
                }
                current += 1;
                queue.clear();
                queue.push(src);
                stamp[src.idx()] = current;
                let mut found = false;
                let mut failed = false;
                let mut head = 0;
                while head < queue.len() && !found {
                    let x = queue[head];
                    head += 1;
                    let ws = &self.watches[(!x).idx()];
                    self.stats.probing_ticks += 1 + ws.len() as u64 / 16;
                    for w in watch::iter(ws) {
                        let Watch::Binary(y) = w else { continue };
                        if (x == src && y == dst) || (x == !dst && y == !src) {
                            continue; // the clause itself (in both directions)
                        }
                        if self.value(y) != 0 || stamp[y.idx()] == current {
                            continue;
                        }
                        if y == dst {
                            found = true;
                            break;
                        }
                        if y == !src {
                            failed = true;
                        }
                        stamp[y.idx()] = current;
                        queue.push(y);
                    }
                }
                if failed && self.value(src) == 0 {
                    // `src` implies `!src`.
                    self.stats.failed += 1;
                    self.learned_unit(!src);
                    if self.propagate().is_some() {
                        self.mark_inconsistent();
                        return false;
                    }
                    break;
                }
                if found {
                    removed += 1;
                    self.delete_binary(!src, dst, true);
                }
            }
        }
        self.stats.transitive_reduced += removed;
        !self.inconsistent
    }
}
