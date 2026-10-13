//! Bounded variable addition, a.k.a. factorization (Kissat `factor.c`).
//!
//! Clauses `(f_i | C_j)` for factors `f_1..f_n` and quotients `C_1..C_m`
//! are replaced by `(x | f_i)` and `(!x | C_j)` with a fresh variable `x`
//! if this reduces the number of clauses.

use crate::arena::CRef;
use crate::solver::{ELIMINATED, Solver};
use crate::types::{Lit, Var};
use crate::watch::{self, Watch};

const FACTOR: i8 = 1;
const QUOTIENT: i8 = 2;
const NOUNTED: i8 = 4;

#[derive(Copy, Clone, PartialEq, Eq)]
enum Entry {
    Binary(Lit),
    Large(CRef),
}

struct Quotient {
    factor: Lit,
    clauses: Vec<Entry>,
    /// Index of the matching clause in the previous quotient.
    matches: Vec<usize>,
}

struct Factoring {
    /// Literals below this bound are not fresh.
    initial: u32,
    /// Occurrences of candidate large clauses (size <= factorsize).
    occs: Vec<Vec<CRef>>,
    /// Number of binary clauses of each literal (kept up to date).
    binaries: Vec<u32>,
    count: Vec<u32>,
    counted: Vec<Lit>,
    nounted: Vec<Lit>,
    qlauses: Vec<CRef>,
    in_quotient: Vec<bool>,
    quotients: Vec<Quotient>,
    fresh: Vec<Var>,
    limit: u64,
}

impl Solver {
    fn factoring_due(&self) -> bool {
        if !self.opts.factor || self.opts.incremental {
            return false;
        }
        let active = (self.vars as u64 - self.eliminated as u64).max(1);
        let log_active = (active as f64).log10() as u64;
        log_active <= self.stats.eliminations + self.opts.factordelay
    }

    pub(crate) fn factor(&mut self) -> bool {
        let start = std::time::Instant::now();
        let res = self.factor_untimed();
        self.stats.time_factor += start.elapsed().as_secs_f64();
        res
    }

    /// Run bounded variable addition at the root level.
    fn factor_untimed(&mut self) -> bool {
        debug_assert_eq!(self.level, 0);
        if self.inconsistent || !self.factoring_due() {
            return !self.inconsistent;
        }
        if self.limits.factor_marked >= self.stats.literals_factor {
            return true;
        }
        self.stats.factorizations += 1;
        let limit = if self.stats.factorizations == 1 {
            self.stats.factor_ticks + self.opts.factoriniticks * 1_000_000
        } else {
            self.stats.factor_ticks
                + self.effort_limit_from(self.last_probe_ticks, self.opts.factoreffort)
        };
        let (bin_before, irr_before) = (self.stats.clauses_binary, self.stats.clauses_irredundant);
        let completed = self.run_factorization(limit);
        if self.verbose(2) {
            println!(
                "c [factor-{}] removed {} binary and {} large clauses",
                self.stats.factorizations,
                bin_before as i64 - self.stats.clauses_binary as i64,
                irr_before as i64 - self.stats.clauses_irredundant as i64
            );
        }
        if completed {
            self.limits.factor_marked = self.stats.literals_factor;
        }
        !self.inconsistent
    }

    fn connect_factor_candidates(&self, f: &mut Factoring) {
        let size_limit = self.opts.factorsize as usize;
        let mut c = 0;
        while (c as usize) < self.arena.len() {
            let next = self.arena.next(c);
            if !self.arena.garbage(c)
                && !self.arena.redundant(c)
                && self.arena.size(c) <= size_limit
            {
                for &l in self.arena.lits(c) {
                    f.occs[l.idx()].push(c);
                }
            }
            c = next;
        }
    }

    /// Binary clauses plus candidate large clauses containing `lit`.
    fn occurrences(&self, f: &Factoring, lit: Lit) -> usize {
        debug_assert_eq!(
            f.binaries[lit.idx()] as usize,
            watch::iter(&self.watches[lit.idx()])
                .filter(|w| matches!(w, Watch::Binary(_)))
                .count()
        );
        f.binaries[lit.idx()] as usize + f.occs[lit.idx()].len()
    }

    fn count_binaries(&self, f: &mut Factoring) {
        f.binaries = self
            .watches
            .iter()
            .map(|ws| {
                watch::iter(ws)
                    .filter(|w| matches!(w, Watch::Binary(_)))
                    .count() as u32
            })
            .collect();
    }

    fn run_factorization(&mut self, limit: u64) -> bool {
        let n = 2 * self.vars;
        let mut f = Factoring {
            initial: n as u32,
            occs: vec![Vec::new(); n],
            binaries: Vec::new(),
            count: vec![0; n],
            counted: Vec::new(),
            nounted: Vec::new(),
            qlauses: Vec::new(),
            in_quotient: Vec::new(),
            quotients: Vec::new(),
            fresh: Vec::new(),
            limit,
        };
        self.connect_factor_candidates(&mut f);
        self.count_binaries(&mut f);
        // Schedule candidate literals by number of occurrences (a max-heap
        // with lazy updates, as candidates change after each factoring).
        let mut schedule: std::collections::BinaryHeap<(usize, std::cmp::Reverse<Lit>)> =
            std::collections::BinaryHeap::new();
        let mut scheduled = 0usize;
        for idx in 0..n {
            let lit = Lit(idx as u32);
            if !self.factor_candidate(lit) {
                continue;
            }
            let occs = self.occurrences(&f, lit);
            if occs > 1 {
                schedule.push((occs, std::cmp::Reverse(lit)));
                scheduled += 1;
            }
        }
        let mut completed = true;
        let mut tried = 0usize;
        while let Some((occs, std::cmp::Reverse(first))) = schedule.pop() {
            if self.stats.factor_ticks > f.limit || self.terminated() || self.inconsistent {
                completed = false;
                break;
            }
            if first.0 >= f.initial || !self.factor_candidate(first) {
                continue;
            }
            let current = self.occurrences(&f, first);
            if current != occs {
                // Stale entry: reschedule with the current count.
                if current > 1 {
                    schedule.push((current, std::cmp::Reverse(first)));
                }
                continue;
            }
            self.clear_factor_flag(first);
            tried += 1;
            if self.first_factor(&mut f, first) > 1 {
                loop {
                    let (next, next_count) = self.next_factor(&mut f);
                    if next == Lit::INVALID || next_count < 2 {
                        break;
                    }
                    self.factorize_next(&mut f, next);
                }
                if let Some((q, reduction)) = best_quotient(&f) {
                    if reduction
                        > (self.elimination_bound as usize)
                            .max(self.opts.factorminreduction as usize)
                    {
                        let touched = self.apply_factoring(&mut f, q);
                        for lit in touched {
                            if lit.0 < f.initial && self.factor_candidate(lit) {
                                let occs = self.occurrences(&f, lit);
                                if occs > 1 {
                                    schedule.push((occs, std::cmp::Reverse(lit)));
                                }
                            }
                        }
                    }
                }
            }
            for q in &f.quotients {
                self.marks[q.factor.idx()] = 0;
            }
            f.quotients.clear();
        }
        let schedule_len = scheduled;
        self.adjust_fresh_variables(&f.fresh);
        if self.verbose(2) {
            println!(
                "c [factor-{}] {} candidates, {} tried, {} fresh, {} ticks, completed {}",
                self.stats.factorizations,
                schedule_len,
                tried,
                f.fresh.len(),
                self.stats.factor_ticks,
                completed
            );
        }
        completed
    }

    fn factor_candidate(&self, lit: Lit) -> bool {
        let v = lit.vidx();
        !self.flags[v].has(ELIMINATED)
            && self.value(lit) == 0
            && self.factor_flags[v] & (1 << lit.negated() as u8) != 0
    }

    fn clear_factor_flag(&mut self, lit: Lit) {
        self.factor_flags[lit.vidx()] &= !(1 << lit.negated() as u8);
    }

    fn first_factor(&mut self, f: &mut Factoring, factor: Lit) -> usize {
        self.marks[factor.idx()] = FACTOR;
        // Duplicated binary clauses must only occur once (otherwise later
        // quotients would match the same clause twice).
        let mut binaries: Vec<Lit> = watch::iter(&self.watches[factor.idx()])
            .filter_map(|w| match w {
                Watch::Binary(other) => Some(other),
                _ => None,
            })
            .collect();
        binaries.sort_unstable();
        binaries.dedup();
        let mut clauses: Vec<Entry> = binaries.into_iter().map(Entry::Binary).collect();
        for &c in &f.occs[factor.idx()] {
            if !self.arena.garbage(c) {
                clauses.push(Entry::Large(c));
            }
        }
        self.stats.factor_ticks += 1 + clauses.len() as u64;
        let res = clauses.len();
        f.quotients.push(Quotient {
            factor,
            clauses,
            matches: Vec::new(),
        });
        res
    }

    /// For a large clause `c` with exactly one factor literal, mark the other
    /// literals as `QUOTIENT` and return the one with fewest occurrences.
    fn quotient_min_lit(&mut self, f: &Factoring, c: CRef) -> Option<Lit> {
        let mut factors = 0;
        let mut min_lit = Lit::INVALID;
        let mut min_size = usize::MAX;
        for i in 0..self.arena.size(c) {
            let other = self.arena.lits(c)[i];
            if self.marks[other.idx()] & FACTOR != 0 {
                factors += 1;
                if factors > 1 {
                    break;
                }
            } else {
                self.marks[other.idx()] |= QUOTIENT;
                let size = f.occs[other.idx()].len();
                if size < min_size {
                    min_size = size;
                    min_lit = other;
                }
            }
        }
        (factors == 1 && min_lit != Lit::INVALID).then_some(min_lit)
    }

    fn unmark_quotient(&mut self, c: CRef) {
        for i in 0..self.arena.size(c) {
            let l = self.arena.lits(c)[i];
            self.marks[l.idx()] &= !QUOTIENT;
        }
    }

    fn mark_qlause(&self, f: &mut Factoring, d: CRef) {
        let d = d as usize;
        if f.in_quotient.len() <= d {
            f.in_quotient.resize(self.arena.len().max(d + 1), false);
        }
        f.in_quotient[d] = true;
        f.qlauses.push(d as CRef);
    }

    fn clear_qlauses(f: &mut Factoring) {
        for &d in &f.qlauses {
            f.in_quotient[d as usize] = false;
        }
        f.qlauses.clear();
    }

    fn next_factor(&mut self, f: &mut Factoring) -> (Lit, u32) {
        let last = f.quotients.len() - 1;
        let clauses = f.quotients[last].clauses.clone();
        let mut ticks = 1 + clauses.len() as u64 / 16;
        for entry in clauses {
            match entry {
                Entry::Binary(q) => {
                    ticks += 1 + self.watches[q.idx()].len() as u64 / 16;
                    for w in watch::iter(&self.watches[q.idx()]) {
                        let Watch::Binary(next) = w else { continue };
                        if next.0 >= f.initial
                            || self.marks[next.idx()] & FACTOR != 0
                            || self.flags[next.vidx()].has(ELIMINATED)
                            || self.value(next) != 0
                        {
                            continue;
                        }
                        if f.count[next.idx()] == 0 {
                            f.counted.push(next);
                        }
                        f.count[next.idx()] += 1;
                    }
                }
                Entry::Large(c) => {
                    ticks += 1;
                    if let Some(min_lit) = self.quotient_min_lit(f, c) {
                        let c_size = self.arena.size(c);
                        ticks += 1 + f.occs[min_lit.idx()].len() as u64;
                        for k in 0..f.occs[min_lit.idx()].len() {
                            let d = f.occs[min_lit.idx()][k];
                            if d == c
                                || self.arena.garbage(d)
                                || f.in_quotient.get(d as usize).copied().unwrap_or(false)
                                || self.arena.size(d) != c_size
                            {
                                continue;
                            }
                            let mut next = Lit::INVALID;
                            let mut ok = true;
                            for &other in self.arena.lits(d) {
                                let mark = self.marks[other.idx()];
                                if mark & QUOTIENT != 0 {
                                    continue;
                                }
                                if mark & (FACTOR | NOUNTED) != 0 || next != Lit::INVALID {
                                    ok = false;
                                    break;
                                }
                                next = other;
                            }
                            if !ok || next == Lit::INVALID || next.0 >= f.initial {
                                continue;
                            }
                            if self.flags[next.vidx()].has(ELIMINATED) || self.value(next) != 0 {
                                continue;
                            }
                            self.marks[next.idx()] |= NOUNTED;
                            f.nounted.push(next);
                            self.mark_qlause(f, d);
                            if f.count[next.idx()] == 0 {
                                f.counted.push(next);
                            }
                            f.count[next.idx()] += 1;
                        }
                        for &l in &f.nounted {
                            self.marks[l.idx()] &= !NOUNTED;
                        }
                        f.nounted.clear();
                    }
                    self.unmark_quotient(c);
                }
            }
            self.stats.factor_ticks += ticks;
            ticks = 0;
            if self.stats.factor_ticks > f.limit {
                break;
            }
        }
        Self::clear_qlauses(f);
        let mut next = Lit::INVALID;
        let mut next_count = 0;
        if self.stats.factor_ticks <= f.limit {
            for &lit in &f.counted {
                let c = f.count[lit.idx()];
                if c > next_count
                    || (c == next_count
                        && next != Lit::INVALID
                        && self.occurrences(f, lit) > self.occurrences(f, next))
                {
                    next_count = c;
                    next = lit;
                }
            }
            if next_count < 2 {
                next = Lit::INVALID;
            }
        }
        for &lit in &f.counted {
            f.count[lit.idx()] = 0;
        }
        f.counted.clear();
        (next, next_count)
    }

    fn factorize_next(&mut self, f: &mut Factoring, next: Lit) {
        let last = f.quotients.len() - 1;
        let last_clauses = f.quotients[last].clauses.clone();
        self.marks[next.idx()] = FACTOR;
        let mut clauses = Vec::new();
        let mut matches = Vec::new();
        for (i, entry) in last_clauses.into_iter().enumerate() {
            match entry {
                Entry::Binary(q) => {
                    let found = watch::iter(&self.watches[q.idx()])
                        .any(|w| matches!(w, Watch::Binary(l) if l == next));
                    if found {
                        clauses.push(Entry::Binary(q));
                        matches.push(i);
                    }
                }
                Entry::Large(c) => {
                    // `next` is now marked as factor; it must not count as a
                    // second factor in `c` (it is not in `c`).
                    if let Some(min_lit) = self.quotient_min_lit(f, c) {
                        let c_size = self.arena.size(c);
                        for k in 0..f.occs[min_lit.idx()].len() {
                            let d = f.occs[min_lit.idx()][k];
                            if d == c
                                || self.arena.garbage(d)
                                || f.in_quotient.get(d as usize).copied().unwrap_or(false)
                                || self.arena.size(d) != c_size
                            {
                                continue;
                            }
                            let ok = self
                                .arena
                                .lits(d)
                                .iter()
                                .all(|&o| self.marks[o.idx()] & QUOTIENT != 0 || o == next);
                            if ok {
                                clauses.push(Entry::Large(d));
                                matches.push(i);
                                self.mark_qlause(f, d);
                                break;
                            }
                        }
                    }
                    self.unmark_quotient(c);
                }
            }
        }
        Self::clear_qlauses(f);
        self.stats.factor_ticks += 1 + clauses.len() as u64;
        f.quotients.push(Quotient {
            factor: next,
            clauses,
            matches,
        });
    }

    /// Returns the literals whose occurrences changed.
    fn apply_factoring(&mut self, f: &mut Factoring, q: usize) -> Vec<Lit> {
        let mut touched: Vec<Lit> = Vec::new();
        // Keep only clauses matched all the way down to quotient `q`.
        for p in (1..=q).rev() {
            let (prev_part, rest) = f.quotients.split_at_mut(p);
            let prev = &mut prev_part[p - 1];
            let cur = &rest[0];
            let prev_is_first = p == 1;
            let mut new_clauses = Vec::with_capacity(cur.clauses.len());
            let mut new_matches = Vec::with_capacity(cur.clauses.len());
            for &j in &cur.matches {
                new_clauses.push(prev.clauses[j]);
                if !prev_is_first {
                    new_matches.push(prev.matches[j]);
                }
            }
            // After flushing, entry i of `prev` matches entry i of `cur`.
            prev.clauses = new_clauses;
            if !prev_is_first {
                prev.matches = new_matches;
            }
            if let Some(cur) = f.quotients.get_mut(p) {
                cur.matches = (0..cur.clauses.len()).collect();
            }
        }
        let fresh_var = self.new_var();
        f.fresh.push(fresh_var);
        let fresh = Lit::new(fresh_var, false);
        f.count.resize(2 * self.vars, 0);
        f.occs.resize(2 * self.vars, Vec::new());
        f.binaries.resize(2 * self.vars, 0);
        self.stats.factored += 1;
        // Dividers (fresh | factor), fresh literal first for RAT.
        for p in 0..=q {
            let factor = f.quotients[p].factor;
            if let Some(proof) = self.proof.as_mut() {
                proof.add(&[fresh, factor]);
            }
            self.new_binary(fresh, factor);
            f.binaries[fresh.idx()] += 1;
            f.binaries[factor.idx()] += 1;
        }
        // Quotients (!fresh | C_j).
        let quotient_factor = f.quotients[q].factor;
        let clauses = f.quotients[q].clauses.clone();
        for entry in clauses {
            match entry {
                Entry::Binary(other) => {
                    if let Some(proof) = self.proof.as_mut() {
                        proof.add(&[!fresh, other]);
                    }
                    self.new_binary(!fresh, other);
                    f.binaries[(!fresh).idx()] += 1;
                    f.binaries[other.idx()] += 1;
                }
                Entry::Large(c) => {
                    let mut lits = vec![!fresh];
                    lits.extend(self.arena.lits(c).iter().filter(|&&l| l != quotient_factor));
                    if let Some(proof) = self.proof.as_mut() {
                        proof.add(&lits);
                    }
                    let d = self.new_large(&lits, false, 0);
                    if lits.len() <= self.opts.factorsize as usize {
                        for &l in &lits {
                            f.occs[l.idx()].push(d);
                        }
                    }
                }
            }
        }
        // Delete the factored clauses.
        for p in 0..=q {
            let factor = f.quotients[p].factor;
            touched.push(factor);
            touched.push(!factor);
            let clauses = f.quotients[p].clauses.clone();
            for entry in clauses {
                match entry {
                    Entry::Binary(other) => {
                        touched.push(other);
                        self.delete_binary(factor, other, true);
                        f.binaries[factor.idx()] -= 1;
                        f.binaries[other.idx()] -= 1;
                    }
                    Entry::Large(c) => {
                        if !self.arena.garbage(c) {
                            // Eagerly disconnect (as Kissat does) so later
                            // candidates do not traverse deleted clauses.
                            for i in 0..self.arena.size(c) {
                                let l = self.arena.lits(c)[i];
                                touched.push(l);
                                let occs = &mut f.occs[l.idx()];
                                if let Some(pos) = occs.iter().position(|&d| d == c) {
                                    occs.remove(pos);
                                }
                            }
                            self.mark_garbage(c);
                        }
                    }
                }
            }
        }
        touched.sort_unstable();
        touched.dedup();
        touched
    }

    /// Fresh variables are put at the front of the decision queue (lowest
    /// priority) with zero score, as in Kissat.
    fn adjust_fresh_variables(&mut self, fresh: &[Var]) {
        for &v in fresh {
            self.heap.update(v, 0.0);
            self.queue.dequeue(v);
        }
        for &v in fresh {
            self.queue.push_front(v);
        }
        if !fresh.is_empty() {
            self.queue.reassign_stamps();
            self.queue.reset_search();
        }
    }
}

/// The quotient with the largest clause reduction.
fn best_quotient(f: &Factoring) -> Option<(usize, usize)> {
    let mut best = None;
    let mut best_reduction = 0;
    for (k, q) in f.quotients.iter().enumerate() {
        let factors = k + 1;
        let quotients = q.clauses.len();
        let before = quotients * factors;
        let after = quotients + factors;
        if before > after {
            let delta = before - after;
            if best.is_none() || best_reduction < delta {
                best_reduction = delta;
                best = Some(k);
            }
        }
    }
    best.map(|k| (k, best_reduction))
}
