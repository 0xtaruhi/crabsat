//! Cheap search heuristics of Kissat 4: lucky assignments (`lucky.c`),
//! decision reordering by clause weights (`reorder.c`) and random decision
//! sequences (`decide.c`).

use crate::solver::{ELIMINATED, Solver};
use crate::stats::logn;
use crate::types::{Lit, Var};
use crate::watch::{self, Watch};

impl Solver {
    fn decidable(&self, v: Var) -> bool {
        !self.flags[v as usize].has(ELIMINATED) && self.values[2 * v as usize] == 0
    }

    // ------------------------------------------------------------------
    // Lucky assignments.

    /// Try a few simple assignments.  Returns true if one satisfies the
    /// formula (the assignment is left on the trail).
    pub(crate) fn lucky(&mut self) -> bool {
        let start = std::time::Instant::now();
        let res = self.lucky_untimed();
        self.stats.time_lucky += start.elapsed().as_secs_f64();
        res
    }

    /// Cheap lucky check before preprocessing: only the constant
    /// assignments, which do not propagate (and thus do not perturb watches)
    /// unless every clause is satisfied by them.
    pub(crate) fn lucky_early(&mut self) -> bool {
        if !self.opts.lucky || self.inconsistent || !self.backtrack_propagate_root() {
            return false;
        }
        // Propagation moves watches, reorders clause literals and touches
        // other search state: restore everything if nothing is found.
        let watches = self.watches.clone();
        let arena = self.arena.mem.clone();
        let assigned = self.assigned.clone();
        let queue = self.queue.clone();
        let heap = self.heap.clone();
        let stats = self.stats.clone();
        let found = self.lucky_untimed();
        if !found {
            self.watches = watches;
            self.arena.mem = arena;
            self.assigned = assigned;
            self.queue = queue;
            self.heap = heap;
            self.stats = stats;
        }
        found
    }

    fn lucky_untimed(&mut self) -> bool {
        if !self.opts.lucky || self.inconsistent || !self.backtrack_propagate_root() {
            return false;
        }

        self.probing = true;
        let found = self.lucky_constant(false)
            || self.lucky_constant(true)
            || self.lucky_sequence(false, false)
            || self.lucky_sequence(false, true)
            || self.lucky_sequence(true, false)
            || self.lucky_sequence(true, true);
        self.probing = false;
        if found {
            self.report('l');
        }
        found
    }

    /// If every clause has a literal of the given polarity (positive if
    /// `positive`), assigning all variables that way satisfies it.
    fn lucky_constant(&mut self, negative: bool) -> bool {
        let ok_lit = |s: &Solver, l: Lit| l.negated() == negative && s.value(l) >= 0;
        for idx in 0..self.watches.len() {
            let lit = Lit(idx as u32);
            if self.value(lit) > 0 {
                continue;
            }
            for w in watch::iter(&self.watches[idx]) {
                if let Watch::Binary(other) = w {
                    if self.value(other) > 0 {
                        continue;
                    }
                    if !ok_lit(self, lit) && !ok_lit(self, other) {
                        return false;
                    }
                }
            }
        }
        let mut c = 0;
        while (c as usize) < self.arena.len() {
            let next = self.arena.next(c);
            if !self.arena.garbage(c) && !self.arena.redundant(c) {
                let lits = self.arena.lits(c);
                if !lits.iter().any(|&l| self.value(l) > 0 || ok_lit(self, l)) {
                    return false;
                }
            }
            c = next;
        }
        self.lucky_assign_all(|v| Lit::new(v, negative), false)
    }

    /// Decide all variables in order (`backward`: from the last) to the
    /// given polarity, flipping a decision once on conflict.
    fn lucky_sequence(&mut self, backward: bool, positive: bool) -> bool {
        self.lucky_assign_all(|v| Lit::new(v, !positive), backward)
    }

    fn lucky_assign_all(&mut self, lit_of: impl Fn(Var) -> Lit, backward: bool) -> bool {
        let n = self.vars as Var;
        for k in 0..n {
            let v = if backward { n - 1 - k } else { k };
            if !self.decidable(v) {
                continue;
            }
            let lit = lit_of(v);
            self.assign_decision(lit);
            if self.propagate().is_none() {
                continue;
            }
            let level = self.level;
            self.backtrack_without_updating_phases(level - 1);
            self.assign_decision(!lit);
            if self.propagate().is_some() {
                self.backtrack_without_updating_phases(0);
                return false;
            }
        }
        debug_assert_eq!(self.unassigned, 0);
        true
    }

    // ------------------------------------------------------------------
    // Reordering.

    pub(crate) fn reordering(&self) -> bool {
        match self.opts.reorder {
            0 => false,
            1 if !self.stable => false,
            _ => self.level == 0 && self.stats.conflicts >= self.limits.reorder_conflicts,
        }
    }

    fn reorder_weights(&self) -> Vec<f64> {
        let max_size = self.opts.reordermaxsize as usize;
        let mut table = vec![0.0; max_size + 1];
        let mut w = 1.0;
        for t in table.iter_mut().skip(2) {
            *t = w;
            w /= 2.0;
        }
        let mut weights = vec![0.0f64; 2 * self.vars];
        let mut c = 0;
        while (c as usize) < self.arena.len() {
            let next = self.arena.next(c);
            if !self.arena.garbage(c) && !self.arena.redundant(c) {
                let lits = self.arena.lits(c);
                if !lits.iter().any(|&l| self.value(l) > 0) {
                    let size = lits
                        .iter()
                        .filter(|&&l| self.value(l) == 0)
                        .count()
                        .clamp(2, max_size);
                    for &l in lits {
                        weights[l.idx()] += table[size];
                    }
                }
            }
            c = next;
        }
        for idx in 0..2 * self.vars {
            let lit = Lit(idx as u32);
            for w in watch::iter(&self.watches[idx]) {
                if let Watch::Binary(other) = w {
                    if lit < other {
                        weights[lit.idx()] += table[2];
                        weights[other.idx()] += table[2];
                    }
                }
            }
        }
        (0..self.vars)
            .map(|v| {
                let (p, n) = (weights[2 * v], weights[2 * v + 1]);
                p.max(n) + 2.0 * p.min(n)
            })
            .collect()
    }

    pub(crate) fn reorder(&mut self) {
        self.stats.reordered += 1;
        let weights = self.reorder_weights();
        let mut sorted: Vec<Var> = (0..self.vars as Var)
            .filter(|&v| !self.flags[v as usize].has(ELIMINATED))
            .collect();
        if self.stable {
            self.rescale_scores_now();
            let heap = &self.heap;
            sorted.sort_by(|&a, &b| {
                weights[a as usize]
                    .total_cmp(&weights[b as usize])
                    .then(heap.score[a as usize].total_cmp(&heap.score[b as usize]))
                    .then(b.cmp(&a))
            });
            for &v in sorted.iter().rev() {
                let s = self.heap.score[v as usize] + weights[v as usize];
                self.heap.update(v, s);
            }
        } else {
            let links = &self.queue.links;
            sorted.sort_by(|&a, &b| {
                weights[a as usize]
                    .total_cmp(&weights[b as usize])
                    .then(links[a as usize].stamp.cmp(&links[b as usize].stamp))
            });
            for &v in &sorted {
                let assigned = self.values[2 * v as usize] != 0;
                self.queue.move_to_front(v, assigned);
            }
        }
        let delta = self.opts.reorderint * self.stats.reordered;
        self.limits.reorder_conflicts = self.stats.conflicts + delta;
        self.report('o');
    }

    // ------------------------------------------------------------------
    // Random decisions.

    pub(crate) fn start_random_sequence(&mut self) {
        if !self.opts.randec || self.stable {
            return;
        }
        if self.randec > 0 {
            return;
        }
        let count = self.stats.random_sequences;
        self.randec = (self.opts.randeclength as f64 * logn(count)) as u64;
        self.stats.random_sequences += 1;
        let delta = self.opts.randecint as f64 * logn(self.stats.random_sequences);
        self.limits.randec_conflicts = self.stats.conflicts + delta as u64;
    }

    pub(crate) fn next_random_decision(&mut self) -> Option<Var> {
        if !self.opts.randec || self.stable || self.warming || self.vars == 0 {
            return None;
        }
        if self.randec == 0 {
            if self.level > 1 || self.stats.conflicts < self.limits.randec_conflicts {
                return None;
            }
            self.start_random_sequence();
        }
        loop {
            self.random = self
                .random
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            let v = ((self.random >> 33) % self.vars as u64) as Var;
            if self.decidable(v) {
                return Some(v);
            }
        }
    }
}
