//! A tiny CDCL solver for small sub-problems (the role of Kissat's
//! `kitten.c`), used by SAT sweeping.
//!
//! It supports assumptions, returns models, and records all learned clauses
//! so that the caller can turn them into proof lines: since assumptions are
//! decisions, every learned clause is implied by the clauses alone.

use crate::types::Lit;

const NO_REASON: u32 = u32::MAX;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum KittenResult {
    Sat,
    Unsat,
    Unknown,
}

#[derive(Default)]
pub struct Kitten {
    vars: usize,
    lits: Vec<Lit>,
    /// Start offset and size of each clause in `lits`.
    clauses: Vec<(u32, u32)>,
    watches: Vec<Vec<u32>>,
    values: Vec<i8>,
    levels: Vec<u32>,
    reasons: Vec<u32>,
    trail: Vec<Lit>,
    propagated: usize,
    /// Trail position of each decision level.
    control: Vec<usize>,
    /// Variables ordered by activity (move-to-front list).
    stamp: Vec<u64>,
    stamp_counter: u64,
    phases: Vec<bool>,
    seen: Vec<bool>,
    /// The formula is inconsistent (empty clause derived).
    inconsistent: bool,
    /// Learned clauses in order (for proofs).
    pub learned: Vec<Vec<Lit>>,
    pub ticks: u64,
}

impl Kitten {
    pub(crate) fn new(vars: usize) -> Kitten {
        Kitten {
            vars,
            watches: vec![Vec::new(); 2 * vars],
            values: vec![0; 2 * vars],
            levels: vec![0; vars],
            reasons: vec![NO_REASON; vars],
            stamp: (0..vars as u64).collect(),
            stamp_counter: vars as u64,
            phases: vec![false; vars],
            seen: vec![false; vars],
            ..Default::default()
        }
    }

    fn level(&self) -> u32 {
        self.control.len() as u32
    }

    fn assign(&mut self, lit: Lit, reason: u32) {
        self.values[lit.idx()] = 1;
        self.values[(!lit).idx()] = -1;
        self.levels[lit.vidx()] = self.level();
        self.reasons[lit.vidx()] = reason;
        self.trail.push(lit);
    }

    /// Add a clause (at level 0 only, before or between solves).
    pub(crate) fn add_clause(&mut self, clause: &[Lit]) {
        self.backtrack(0);
        if self.inconsistent {
            return;
        }
        let mut lits: Vec<Lit> = Vec::with_capacity(clause.len());
        for &l in clause {
            match self.values[l.idx()] {
                v if v > 0 && self.levels[l.vidx()] == 0 => return,
                v if v < 0 && self.levels[l.vidx()] == 0 => {}
                _ => {
                    if lits.contains(&!l) {
                        return;
                    }
                    if !lits.contains(&l) {
                        lits.push(l);
                    }
                }
            }
        }
        self.add_internal(&lits);
    }

    fn add_internal(&mut self, lits: &[Lit]) -> u32 {
        match lits.len() {
            0 => {
                self.inconsistent = true;
                NO_REASON
            }
            1 => {
                if self.values[lits[0].idx()] == 0 {
                    self.assign(lits[0], NO_REASON);
                } else if self.values[lits[0].idx()] < 0 {
                    self.inconsistent = true;
                }
                NO_REASON
            }
            _ => {
                let c = self.clauses.len() as u32;
                self.clauses
                    .push((self.lits.len() as u32, lits.len() as u32));
                self.lits.extend_from_slice(lits);
                self.watches[lits[0].idx()].push(c);
                self.watches[lits[1].idx()].push(c);
                c
            }
        }
    }

    fn propagate(&mut self) -> Option<u32> {
        while self.propagated < self.trail.len() {
            let lit = self.trail[self.propagated];
            self.propagated += 1;
            let not_lit = !lit;
            let mut ws = std::mem::take(&mut self.watches[not_lit.idx()]);
            self.ticks += 1 + ws.len() as u64 / 8;
            let mut i = 0;
            let mut j = 0;
            let mut conflict = None;
            while i < ws.len() {
                let c = ws[i];
                i += 1;
                let (s, n) = self.clauses[c as usize];
                let s = s as usize;
                let n = n as usize;
                if self.lits[s] == not_lit {
                    self.lits.swap(s, s + 1);
                }
                let other = self.lits[s];
                if self.values[other.idx()] > 0 {
                    ws[j] = c;
                    j += 1;
                    continue;
                }
                self.ticks += 1;
                let mut found = false;
                for k in 2..n {
                    let r = self.lits[s + k];
                    if self.values[r.idx()] >= 0 {
                        self.lits.swap(s + 1, s + k);
                        self.watches[r.idx()].push(c);
                        found = true;
                        break;
                    }
                }
                if found {
                    continue;
                }
                ws[j] = c;
                j += 1;
                if self.values[other.idx()] < 0 {
                    conflict = Some(c);
                    while i < ws.len() {
                        ws[j] = ws[i];
                        i += 1;
                        j += 1;
                    }
                    break;
                }
                self.assign(other, c);
            }
            ws.truncate(j);
            self.watches[not_lit.idx()] = ws;
            if conflict.is_some() {
                return conflict;
            }
        }
        None
    }

    fn backtrack(&mut self, level: u32) {
        if self.level() <= level {
            return;
        }
        let pos = self.control[level as usize];
        for &l in &self.trail[pos..] {
            self.values[l.idx()] = 0;
            self.values[(!l).idx()] = 0;
            self.phases[l.vidx()] = !l.negated();
            self.reasons[l.vidx()] = NO_REASON;
        }
        self.trail.truncate(pos);
        self.control.truncate(level as usize);
        self.propagated = pos;
    }

    /// Analyze a conflict; returns the learned clause (asserting literal
    /// first) and the backjump level.
    fn analyze(&mut self, conflict: u32) -> (Vec<Lit>, u32) {
        let level = self.level();
        let mut learned = vec![Lit::INVALID];
        let mut open = 0;
        let mut reason = conflict;
        let mut t = self.trail.len();
        let mut uip;
        let mut seen_vars = Vec::new();
        loop {
            let (s, n) = self.clauses[reason as usize];
            for k in 0..n as usize {
                let l = self.lits[s as usize + k];
                let v = l.vidx();
                if self.seen[v] || self.levels[v] == 0 {
                    continue;
                }
                self.seen[v] = true;
                seen_vars.push(v);
                if self.levels[v] == level {
                    open += 1;
                } else {
                    learned.push(l);
                }
            }
            loop {
                t -= 1;
                uip = self.trail[t];
                if self.seen[uip.vidx()] {
                    break;
                }
            }
            open -= 1;
            if open == 0 {
                break;
            }
            reason = self.reasons[uip.vidx()];
            // Skip the propagated literal itself when resolving.
            self.seen[uip.vidx()] = true;
        }
        learned[0] = !uip;
        for v in seen_vars {
            self.seen[v] = false;
            self.stamp_counter += 1;
            self.stamp[v] = self.stamp_counter;
        }
        let mut jump = 0;
        let mut pos = 0;
        for (k, l) in learned.iter().enumerate().skip(1) {
            let lv = self.levels[l.vidx()];
            if lv > jump {
                jump = lv;
                pos = k;
            }
        }
        if pos > 1 {
            learned.swap(1, pos);
        }
        (learned, jump)
    }

    fn decide(&mut self) -> bool {
        self.ticks += 1 + self.vars as u64 / 16;
        let mut best = usize::MAX;
        let mut best_stamp = 0;
        for v in 0..self.vars {
            if self.values[2 * v] == 0 && (best == usize::MAX || self.stamp[v] > best_stamp) {
                best = v;
                best_stamp = self.stamp[v];
            }
        }
        if best == usize::MAX {
            return false;
        }
        self.control.push(self.trail.len());
        let lit = Lit::new(best as u32, !self.phases[best]);
        self.assign(lit, NO_REASON);
        true
    }

    /// Solve under assumptions with a tick limit.
    pub(crate) fn solve(&mut self, assumptions: &[Lit], tick_limit: u64) -> KittenResult {
        self.backtrack(0);
        if self.inconsistent {
            return KittenResult::Unsat;
        }
        let limit = self.ticks + tick_limit;
        loop {
            if let Some(conflict) = self.propagate() {
                if self.level() == 0 {
                    self.inconsistent = true;
                    self.learned.push(Vec::new());
                    return KittenResult::Unsat;
                }
                let (learned, jump) = self.analyze(conflict);
                self.learned.push(learned.clone());
                self.backtrack(jump);
                let c = self.add_internal(&learned);
                if learned.len() >= 2 {
                    self.assign(learned[0], c);
                }
                continue;
            }
            if self.ticks > limit {
                self.backtrack(0);
                return KittenResult::Unknown;
            }
            let level = self.level() as usize;
            if level < assumptions.len() {
                let a = assumptions[level];
                match self.values[a.idx()] {
                    v if v > 0 => {
                        // Already satisfied: open an empty level.
                        self.control.push(self.trail.len());
                    }
                    v if v < 0 => {
                        // Failed assumption.
                        self.backtrack(0);
                        return KittenResult::Unsat;
                    }
                    _ => {
                        self.control.push(self.trail.len());
                        self.assign(a, NO_REASON);
                    }
                }
                continue;
            }
            if !self.decide() {
                return KittenResult::Sat;
            }
        }
    }

    /// Model value after `Sat` (before the next solve or clause addition).
    pub(crate) fn model_value(&self, lit: Lit) -> bool {
        self.values[lit.idx()] > 0
    }

    pub(crate) fn is_inconsistent(&self) -> bool {
        self.inconsistent
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn l(d: i32) -> Lit {
        Lit::from_dimacs(d)
    }

    #[test]
    fn small() {
        let mut k = Kitten::new(3);
        k.add_clause(&[l(1), l(2)]);
        k.add_clause(&[l(-1), l(2)]);
        k.add_clause(&[l(1), l(-2), l(3)]);
        assert_eq!(k.solve(&[], 1 << 20), KittenResult::Sat);
        assert!(k.model_value(l(2)));
        assert_eq!(k.solve(&[l(-2)], 1 << 20), KittenResult::Unsat);
        assert_eq!(k.solve(&[l(-3)], 1 << 20), KittenResult::Sat);
        assert!(k.model_value(l(1)));
    }

    #[test]
    fn pigeon_hole() {
        // 4 pigeons, 3 holes.
        let var = |p: i32, h: i32| l(p * 3 + h + 1);
        let mut k = Kitten::new(12);
        for p in 0..4 {
            k.add_clause(&[var(p, 0), var(p, 1), var(p, 2)]);
        }
        for h in 0..3 {
            for p in 0..4 {
                for q in p + 1..4 {
                    k.add_clause(&[!var(p, h), !var(q, h)]);
                }
            }
        }
        assert_eq!(k.solve(&[], 1 << 30), KittenResult::Unsat);
    }
}
