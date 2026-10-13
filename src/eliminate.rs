//! Bounded variable elimination with gate detection and forward
//! subsumption (Kissat `eliminate.c`, `resolve.c`, `gates.c`, `ands.c`,
//! `equivalences.c`, `forward.c`).

use crate::arena::CRef;
use crate::simplify::Simplified;
use crate::solver::{ELIMINATE, ELIMINATED, SUBSUME, Solver};
use crate::stats::nlogpown;
use crate::types::{Lit, Var};
use crate::watch::{self, Watch};

/// A clause in an occurrence list: binary (stored as its other literal) or
/// large.
#[derive(Copy, Clone)]
enum Occ {
    Binary(Lit),
    Large(CRef),
}

/// Clauses of one side of an elimination candidate.
#[derive(Default)]
struct Side {
    occs: Vec<Occ>,
    gate: Vec<bool>,
}

impl Solver {
    /// Kissat's `kissat_scale_delta`: scale intervals by formula size.
    pub fn scale_delta(&self, delta: u64) -> u64 {
        let clauses = self.stats.clauses_irredundant + self.stats.clauses_binary;
        let f = ((clauses + 1 + 9) as f64).log10() - 5.0;
        let ff = 4.5 * f * f + 25.0;
        (ff * delta as f64) as u64
    }

    pub fn eliminating(&self) -> bool {
        if !self.opts.simplify || !self.opts.eliminate {
            return false;
        }
        if self.stats.clauses_irredundant == 0 {
            return false;
        }
        if self.last_reduce_conflicts == self.stats.conflicts {
            return false;
        }
        if self.limits.eliminate_conflicts > self.stats.conflicts {
            return false;
        }
        self.limits.eliminate_variables < self.stats.variables_eliminate
            || self.limits.subsume_variables < self.stats.variables_subsume
    }

    pub fn eliminate(&mut self) -> bool {
        let start = std::time::Instant::now();
        let res = self.eliminate_untimed();
        self.stats.time_eliminate += start.elapsed().as_secs_f64();
        res
    }

    /// Run variable elimination.  Returns false if the formula became
    /// unsatisfiable.
    fn eliminate_untimed(&mut self) -> bool {
        if !self.backtrack_propagate_root() {
            return false;
        }
        self.stats.eliminations += 1;
        let before = self.stats.eliminated;
        self.enter_dense_mode();
        if !self.inconsistent {
            self.eliminate_variables();
        }
        self.resume_sparse_mode();
        let delta = self.opts.eliminateint as f64 * nlogpown(self.stats.eliminations, 2);
        self.limits.eliminate_conflicts = self.stats.conflicts + self.scale_delta(delta as u64);
        self.last_eliminate_ticks = self.stats.search_ticks;
        self.recount_phase_heights();
        if self.compacting() && !self.compact() {
            return false;
        }
        if self.verbose(2) {
            println!(
                "c [eliminate-{}] eliminated {} variables (total {})",
                self.stats.eliminations,
                self.stats.eliminated - before,
                self.stats.eliminated
            );
        }
        self.report('e');
        !self.inconsistent
    }

    fn effort_limit(&self, last_ticks: u64, effort: u64) -> u64 {
        let reference = self.stats.search_ticks - last_ticks;
        let reference = reference.max(1_000_000 * self.opts.mineffort);
        (reference as f64 * effort as f64 * 1e-3) as u64
    }

    fn eliminate_variables(&mut self) {
        let limit = self.stats.eliminate_resolutions
            + self.effort_limit(self.last_eliminate_ticks, self.opts.eliminateeffort);
        let mut complete = false;
        let mut remain = 0;
        let mut eliminated_last_round = 0;
        for round in 1..=self.opts.eliminaterounds {
            complete = self.forward_subsume();
            if self.inconsistent || !self.dense_propagate() {
                return;
            }
            let schedule = self.schedule_variables();
            eliminated_last_round = 0;
            remain = 0;
            for (k, &v) in schedule.iter().enumerate() {
                if self.stats.eliminate_resolutions > limit || self.terminated() {
                    complete = false;
                    remain = schedule.len() - k;
                    break;
                }
                if self.flags[v as usize] & ELIMINATE == 0 {
                    continue;
                }
                if self.eliminate_variable(v) {
                    eliminated_last_round += 1;
                }
                if self.inconsistent || !self.dense_propagate() {
                    return;
                }
            }
            if eliminated_last_round > 0 {
                complete = false;
            }
            if complete || round == self.opts.eliminaterounds {
                break;
            }
            if self.stats.eliminate_resolutions > limit {
                break;
            }
        }
        let complete = complete && remain == 0 && eliminated_last_round == 0;
        self.set_next_elimination_bound(complete);
    }

    fn set_next_elimination_bound(&mut self, complete: bool) {
        let max_bound = self.opts.eliminatebound;
        let current = self.elimination_bound;
        if complete {
            if current == max_bound {
                self.limits.eliminate_variables = self.stats.variables_eliminate;
                self.limits.subsume_variables = self.stats.variables_subsume;
            } else {
                self.elimination_bound = if current == 0 {
                    1
                } else {
                    (2 * current).min(max_bound)
                };
                for f in &mut self.flags {
                    *f |= ELIMINATE;
                }
                self.limits.eliminate_variables = 0;
            }
        } else {
            for f in &mut self.flags {
                *f &= !ELIMINATE;
            }
        }
    }

    /// Candidate variables ordered by increasing occurrence score.
    fn schedule_variables(&mut self) -> Vec<Var> {
        let occlim = self.opts.eliminateocclim as f64;
        let mut scored: Vec<(f64, Var)> = Vec::new();
        for v in 0..self.vars as Var {
            if self.flags[v as usize] & (ELIMINATE | ELIMINATED) != ELIMINATE {
                continue;
            }
            let pos = Lit::new(v, false);
            if self.value(pos) != 0 {
                continue;
            }
            let p = (self.watches[pos.idx()].len() as f64).min(occlim);
            let n = (self.watches[(!pos).idx()].len() as f64).min(occlim);
            scored.push((p * n - p - n, v));
        }
        scored.sort_by(|a, b| a.0.total_cmp(&b.0));
        scored.into_iter().map(|(_, v)| v).collect()
    }

    /// Clean the occurrence list of `lit` (remove garbage large clauses) and
    /// return its clauses; satisfied clauses are marked as garbage.
    fn gather_occurrences(&mut self, lit: Lit, side: &mut Side) -> bool {
        side.occs.clear();
        side.gate.clear();
        let mut ws = std::mem::take(&mut self.watches[lit.idx()]);
        let mut j = 0;
        let mut i = 0;
        let mut ok = true;
        let clslim = self.opts.eliminateclslim as usize;
        while i < ws.len() {
            let head = ws[i];
            if watch::is_binary(head) {
                ws[j] = head;
                i += 1;
                j += 1;
                let other = watch::head_lit(head);
                if self.value(other) > 0 {
                    continue;
                }
                side.occs.push(Occ::Binary(other));
            } else {
                let c = ws[i + 1];
                i += 2;
                if self.arena.garbage(c) {
                    continue;
                }
                ws[j] = head;
                ws[j + 1] = c;
                j += 2;
                if self.arena.lits(c).iter().any(|&l| self.value(l) > 0) {
                    continue;
                }
                if self.arena.size(c) > clslim {
                    ok = false;
                }
                side.occs.push(Occ::Large(c));
            }
        }
        ws.truncate(j);
        self.watches[lit.idx()] = ws;
        side.gate.resize(side.occs.len(), false);
        ok
    }

    /// Literals of an occurrence (including the pivot `lit`).
    fn occ_lits(&self, lit: Lit, occ: Occ, out: &mut Vec<Lit>) {
        out.clear();
        match occ {
            Occ::Binary(other) => {
                out.push(lit);
                out.push(other);
            }
            Occ::Large(c) => out.extend_from_slice(self.arena.lits(c)),
        }
    }

    /// Find an AND gate (or equivalence) defining `lit`:
    /// `lit = l1 & ... & ln` as binary clauses `(!lit | li)` and one base
    /// clause `(lit | !l1 | ... | !ln)`.  Marks gate clauses in `pos`/`neg`
    /// where `pos` are the clauses of `lit` and `neg` those of `!lit`.
    fn find_and_gate(&mut self, lit: Lit, pos: &mut Side, neg: &mut Side) -> bool {
        // Mark all li with binary clauses (!lit | li).
        let mut marked = Vec::new();
        for occ in &neg.occs {
            if let Occ::Binary(other) = *occ
                && self.value(other) == 0
                && self.marks[other.idx()] == 0
            {
                self.marks[other.idx()] = 1;
                marked.push(other);
            }
        }
        let mut found = None;
        if !marked.is_empty() {
            for (k, occ) in pos.occs.iter().enumerate() {
                let ok = match *occ {
                    Occ::Binary(other) => self.marks[(!other).idx()] != 0,
                    Occ::Large(c) => self
                        .arena
                        .lits(c)
                        .iter()
                        .all(|&l| l == lit || self.value(l) < 0 || self.marks[(!l).idx()] != 0),
                };
                if ok {
                    found = Some(k);
                    break;
                }
            }
        }
        if let Some(k) = found {
            pos.gate[k] = true;
            // Mark the inputs used by the base clause.
            let mut lits = Vec::new();
            self.occ_lits(lit, pos.occs[k], &mut lits);
            for &l in &marked {
                self.marks[l.idx()] = 0;
            }
            for &l in &lits {
                if l != lit {
                    self.marks[(!l).idx()] = 1;
                }
            }
            for (m, occ) in neg.occs.iter().enumerate() {
                if let Occ::Binary(other) = *occ
                    && self.marks[other.idx()] != 0
                {
                    neg.gate[m] = true;
                    self.marks[other.idx()] = 0; // only one binary per input
                }
            }
            for &l in &lits {
                if l != lit {
                    self.marks[(!l).idx()] = 0;
                }
            }
            true
        } else {
            for &l in &marked {
                self.marks[l.idx()] = 0;
            }
            false
        }
    }

    /// Find an if-then-else gate `lit = c ? t : e` given by the clauses
    /// `(!c | !t | lit) (c | !e | lit)` in `pos` and `(!c | t | !lit)
    /// (c | e | !lit)` in `neg`.
    fn find_ite_gate(&mut self, lit: Lit, pos: &mut Side, neg: &mut Side) -> bool {
        let ternary = |s: &Solver, occ: Occ, pivot: Lit| -> Option<(Lit, Lit)> {
            if let Occ::Large(c) = occ {
                let lits = s.arena.lits(c);
                if lits.len() == 3 {
                    let mut o = lits.iter().copied().filter(|&l| l != pivot);
                    let (a, b) = (o.next()?, o.next()?);
                    return Some(if a < b { (a, b) } else { (b, a) });
                }
            }
            None
        };
        // Other literal pairs of the ternary clauses on the negative side.
        let mut neg_pairs: crate::fxhash::FxHashMap<(Lit, Lit), usize> = Default::default();
        for (k, &occ) in neg.occs.iter().enumerate() {
            if let Some(pair) = ternary(self, occ, !lit) {
                neg_pairs.insert(pair, k);
            }
        }
        if neg_pairs.len() < 2 {
            return false;
        }
        let key = |a: Lit, b: Lit| if a < b { (a, b) } else { (b, a) };
        let pos_ternaries: Vec<(usize, (Lit, Lit))> = pos
            .occs
            .iter()
            .enumerate()
            .filter_map(|(k, &occ)| ternary(self, occ, lit).map(|p| (k, p)))
            .collect();
        for &(i, (a, b)) in &pos_ternaries {
            // (!c | !t | lit) with {!c, !t} = {a, b}.
            for (nc, nt) in [(a, b), (b, a)] {
                let (c, t) = (!nc, !nt);
                let Some(&j) = neg_pairs.get(&key(!c, t)) else {
                    continue;
                };
                // Find (c | !e | lit) in pos and (c | e | !lit) in neg.
                for &(k, (x, y)) in &pos_ternaries {
                    if k == i {
                        continue;
                    }
                    let ne = if x == c {
                        y
                    } else if y == c {
                        x
                    } else {
                        continue;
                    };
                    let e = !ne;
                    if e.var() == t.var() || e.var() == c.var() {
                        continue;
                    }
                    let Some(&m) = neg_pairs.get(&key(c, e)) else {
                        continue;
                    };
                    pos.gate[i] = true;
                    pos.gate[k] = true;
                    neg.gate[j] = true;
                    neg.gate[m] = true;
                    return true;
                }
            }
        }
        false
    }

    /// Find an XOR gate: all clauses over the same variable set of size
    /// 3..=arity+1 containing the pivot with one parity of negations.
    fn find_xor_gate(&mut self, _lit: Lit, pos: &mut Side, neg: &mut Side) -> bool {
        let max_size = self.opts.congruencexorarity as usize + 1;
        // (sorted variable set) -> (side, index, negation mask) of clauses.
        let mut groups: crate::fxhash::FxHashMap<Vec<u32>, Vec<(bool, usize, u32)>> =
            Default::default();
        for (side_is_pos, side) in [(true, &*pos), (false, &*neg)] {
            for (k, &occ) in side.occs.iter().enumerate() {
                let Occ::Large(c) = occ else { continue };
                let lits = self.arena.lits(c);
                if lits.len() < 3 || lits.len() > max_size {
                    continue;
                }
                let mut sorted = lits.to_vec();
                sorted.sort_unstable_by_key(|l| l.var());
                let vars: Vec<u32> = sorted.iter().map(|l| l.var()).collect();
                if vars.windows(2).any(|w| w[0] == w[1]) {
                    continue;
                }
                let mask = sorted
                    .iter()
                    .enumerate()
                    .fold(0u32, |m, (i, l)| m | ((l.negated() as u32) << i));
                groups.entry(vars).or_default().push((side_is_pos, k, mask));
            }
        }
        for (vars, clauses) in groups {
            let size = vars.len();
            let needed = 1usize << (size - 1);
            if clauses.len() < needed {
                continue;
            }
            for parity in 0..2u32 {
                let mut present: Vec<Option<(bool, usize)>> = vec![None; 1 << size];
                for &(side, k, mask) in &clauses {
                    if mask.count_ones() % 2 == parity {
                        present[mask as usize] = Some((side, k));
                    }
                }
                let complete = (0..1u32 << size)
                    .filter(|m| m.count_ones() % 2 == parity)
                    .all(|m| present[m as usize].is_some());
                if !complete {
                    continue;
                }
                for (side, k) in present.into_iter().flatten() {
                    if side {
                        pos.gate[k] = true;
                    } else {
                        neg.gate[k] = true;
                    }
                }
                return true;
            }
        }
        false
    }

    /// Try to eliminate variable `v`.
    fn eliminate_variable(&mut self, v: Var) -> bool {
        self.flags[v as usize] &= !ELIMINATE;
        let pos_lit = Lit::new(v, false);
        if self.value(pos_lit) != 0 || self.flags[v as usize] & ELIMINATED != 0 {
            return false;
        }
        let mut pos = Side::default();
        let mut neg = Side::default();
        if !self.gather_occurrences(pos_lit, &mut pos)
            || !self.gather_occurrences(!pos_lit, &mut neg)
        {
            return false;
        }
        let occlim = self.opts.eliminateocclim as usize;
        if pos.occs.len() > occlim || neg.occs.len() > occlim {
            return false;
        }
        // Resolve on the side with fewer clauses as `lit`.
        let (lit, mut pos, mut neg) = if pos.occs.len() <= neg.occs.len() {
            (pos_lit, pos, neg)
        } else {
            (!pos_lit, neg, pos)
        };
        let gates = (self.opts.ands
            && (self.find_and_gate(lit, &mut pos, &mut neg)
                || self.find_and_gate(!lit, &mut neg, &mut pos)))
            || (self.opts.ifthenelse && self.find_ite_gate(lit, &mut pos, &mut neg))
            || (self.opts.xors && self.find_xor_gate(lit, &mut pos, &mut neg));
        let bound = pos.occs.len() + neg.occs.len() + self.elimination_bound as usize;
        let Some(resolvents) = self.resolve(lit, &pos, &neg, gates, bound) else {
            return false;
        };
        if std::env::var("CRABSAT_TRACE_VAR")
            .ok()
            .and_then(|x| x.parse::<u32>().ok())
            == Some(v + 1)
        {
            let show = |s: &Solver, side_lit: Lit, side: &Side| {
                let mut out = Vec::new();
                for (k, &occ) in side.occs.iter().enumerate() {
                    let mut l = Vec::new();
                    s.occ_lits(side_lit, occ, &mut l);
                    let d: Vec<String> = l
                        .iter()
                        .map(|x| {
                            format!(
                                "{}{}",
                                x,
                                match s.value(*x) {
                                    0 => "",
                                    v if v > 0 => "T",
                                    _ => "F",
                                }
                            )
                        })
                        .collect();
                    out.push(format!("{}{:?}", if side.gate[k] { "G" } else { "" }, d));
                }
                out
            };
            eprintln!(
                "ELIM {} gates {} pos {:?}",
                lit,
                gates,
                show(self, lit, &pos)
            );
            eprintln!("ELIM neg {:?}", show(self, !lit, &neg));
            for r in &resolvents {
                eprintln!("ELIM resolvent {:?}", r);
            }
        }
        // Add resolvents.
        for r in &resolvents {
            if let Some(p) = self.proof.as_mut() {
                p.add(r);
            }
            match r.len() {
                0 => {
                    self.mark_inconsistent();
                    break;
                }
                1 => {
                    if self.value(r[0]) == 0 {
                        self.assign_unit(r[0]);
                    } else if self.value(r[0]) < 0 {
                        self.mark_inconsistent();
                        break;
                    }
                }
                2 => self.new_binary(r[0], r[1]),
                _ => {
                    let c = self.new_large(r, false, 0);
                    // `new_large` watched the first two literals; in dense
                    // mode clauses are connected through all literals.
                    self.unwatch_clause(c);
                    self.connect_occurrences(c);
                }
            }
            for &l in r {
                self.mark_added_var(l.vidx());
                self.mark_removed_var(l.vidx());
            }
        }
        // Save clauses on the extension stack and remove them.
        let mut lits = Vec::new();
        for &occ in &pos.occs {
            self.occ_lits(lit, occ, &mut lits);
            self.push_extension(lit, &lits);
        }
        if !neg.occs.is_empty() {
            self.push_extension(!lit, &[!lit]);
        }
        for (side_lit, side) in [(lit, &pos), (!lit, &neg)] {
            for &occ in &side.occs {
                match occ {
                    Occ::Binary(other) => {
                        if self.value(other) <= 0 {
                            self.delete_binary(side_lit, other, true);
                        }
                    }
                    Occ::Large(c) => {
                        if !self.arena.garbage(c) {
                            self.mark_garbage(c);
                        }
                    }
                }
            }
        }
        // Satisfied binary clauses of the pivot are still connected.
        for l in [lit, !lit] {
            let ws = std::mem::take(&mut self.watches[l.idx()]);
            for w in watch::iter(&ws) {
                if let Watch::Binary(other) = w {
                    watch::remove_binary(&mut self.watches[other.idx()], l);
                    self.stats.clauses_binary -= 1;
                    if let Some(p) = self.proof.as_mut() {
                        p.delete(&[l, other]);
                    }
                }
            }
        }
        self.flags[v as usize] |= ELIMINATED;
        self.flags[v as usize] &= !(ELIMINATE | SUBSUME);
        self.eliminated += 1;
        self.stats.eliminated += 1;
        self.unassigned -= 1;
        self.queue.dequeue(v);
        true
    }

    /// Compute all non-tautological resolvents on `lit`, or `None` if there
    /// are more than `bound` (or one is too long).
    fn resolve(
        &mut self,
        lit: Lit,
        pos: &Side,
        neg: &Side,
        gates: bool,
        bound: usize,
    ) -> Option<Vec<Vec<Lit>>> {
        let clslim = self.opts.eliminateclslim as usize;
        let mut res: Vec<Vec<Lit>> = Vec::new();
        let mut a = Vec::new();
        let mut b = Vec::new();
        for (i, &p) in pos.occs.iter().enumerate() {
            self.occ_lits(lit, p, &mut a);
            a.retain(|&l| l != lit && self.value(l) == 0);
            for &l in &a {
                self.marks[l.idx()] = 1;
            }
            let mut failed = false;
            for (j, &n) in neg.occs.iter().enumerate() {
                if gates && pos.gate[i] == neg.gate[j] {
                    continue;
                }
                self.stats.eliminate_resolutions += 1;
                self.occ_lits(!lit, n, &mut b);
                let mut resolvent = a.clone();
                let mut tautological = false;
                for &l in &b {
                    if l == !lit || self.value(l) < 0 || self.marks[l.idx()] != 0 {
                        continue;
                    }
                    if self.marks[(!l).idx()] != 0 {
                        tautological = true;
                        break;
                    }
                    resolvent.push(l);
                }
                if tautological {
                    continue;
                }
                if res.len() >= bound || resolvent.len() > clslim {
                    failed = true;
                    break;
                }
                res.push(resolvent);
            }
            for &l in &a {
                self.marks[l.idx()] = 0;
            }
            if failed {
                return None;
            }
        }
        Some(res)
    }

    // ------------------------------------------------------------------
    // Forward subsumption (in dense mode).

    /// Forward subsumption and strengthening of irredundant large clauses.
    /// Returns true if all candidates were tried.
    fn forward_subsume(&mut self) -> bool {
        let clslim = self.opts.subsumeclslim as usize;
        // All clauses are connected (they may subsume others) but only those
        // with a flagged variable are checked.
        let mut candidates: Vec<(usize, CRef, bool)> = Vec::new();
        let mut c = 0;
        while (c as usize) < self.arena.len() {
            let next = self.arena.next(c);
            if !self.arena.garbage(c) && !self.arena.redundant(c) {
                let size = self.arena.size(c);
                if size <= clslim {
                    let flagged = self
                        .arena
                        .lits(c)
                        .iter()
                        .any(|l| self.flags[l.vidx()] & SUBSUME != 0);
                    candidates.push((size, c, flagged));
                }
            }
            c = next;
        }
        candidates.sort_unstable();
        let limit = self.stats.eliminate_resolutions
            + self.effort_limit(self.last_eliminate_ticks, self.opts.forwardeffort);
        let mut one_watch: Vec<Vec<CRef>> = vec![Vec::new(); 2 * self.vars];
        let mut complete = true;
        let mut checks = 0u64;
        let mut lits: Vec<Lit> = Vec::new();
        for &(_, c, flagged) in &candidates {
            if checks > limit {
                complete = false;
                break;
            }
            if self.arena.garbage(c) {
                continue;
            }
            if self.simplify_clause_at_root(c) != Simplified::Large {
                continue;
            }
            lits.clear();
            lits.extend_from_slice(self.arena.lits(c));
            for &l in &lits {
                self.marks[l.idx()] = 1;
            }
            let mut subsumed = false;
            let mut remove = Lit::INVALID;
            'search: for &l in if flagged { &lits[..] } else { &[] } {
                // Binary clauses (l | o): subsume if o in c, strengthen if !o
                // in c.  Binary (!l | o) with o in c removes l.
                for (from, neg) in [(l, false), (!l, true)] {
                    for w in watch::iter(&self.watches[from.idx()]) {
                        if let Watch::Binary(o) = w {
                            checks += 1;
                            if self.marks[o.idx()] != 0 {
                                if neg {
                                    remove = l;
                                } else {
                                    subsumed = true;
                                }
                                break 'search;
                            }
                            if !neg && self.marks[(!o).idx()] != 0 {
                                remove = !o;
                                break 'search;
                            }
                        }
                    }
                }
                for (from, neg) in [(l, false), (!l, true)] {
                    for &d in &one_watch[from.idx()] {
                        if self.arena.garbage(d) {
                            continue;
                        }
                        checks += 1;
                        // Check d \ {!l} subset of c (neg) or d subset of c.
                        let mut negated = Lit::INVALID;
                        let mut ok = true;
                        for &x in self.arena.lits(d) {
                            if self.marks[x.idx()] != 0 {
                                continue;
                            }
                            if negated == Lit::INVALID && self.marks[(!x).idx()] != 0 {
                                negated = x;
                                continue;
                            }
                            ok = false;
                            break;
                        }
                        if !ok {
                            continue;
                        }
                        if negated == Lit::INVALID {
                            subsumed = true;
                        } else {
                            let _ = neg;
                            remove = !negated;
                        }
                        break 'search;
                    }
                }
            }
            for &l in &lits {
                self.marks[l.idx()] = 0;
            }
            if subsumed {
                self.stats.subsumed += 1;
                self.mark_garbage(c);
                continue;
            }
            if remove != Lit::INVALID {
                self.stats.strengthened += 1;
                watch::remove_large(&mut self.watches[remove.idx()], c);
                let new_lits: Vec<Lit> = lits.iter().copied().filter(|&l| l != remove).collect();
                if self.strengthen_to(c, &new_lits) != Simplified::Large {
                    if self.inconsistent {
                        return false;
                    }
                    continue;
                }
                lits = new_lits;
            }
            // Connect through the literal with the fewest occurrences.
            let best = *lits
                .iter()
                .min_by_key(|l| self.watches[l.idx()].len() + self.watches[(!**l).idx()].len())
                .unwrap();
            one_watch[best.idx()].push(c);
        }
        if complete {
            for f in &mut self.flags {
                *f &= !SUBSUME;
            }
        }
        complete
    }
}
