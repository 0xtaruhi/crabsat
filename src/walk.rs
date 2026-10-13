//! Local search for rephasing (Kissat `walk.c`): ProbSAT on the
//! irredundant clauses starting from the saved phases.  The assignment with
//! the fewest falsified clauses is written back to the saved phases.

use crate::solver::{ELIMINATED, Solver};
use crate::types::Lit;
use crate::watch::{self, Watch};

/// (average clause size, cb) pairs used to fit the ProbSAT base.
const CBVALS: [(f64, f64); 6] = [
    (0.0, 2.0),
    (3.0, 2.5),
    (4.0, 2.85),
    (5.0, 3.7),
    (6.0, 5.1),
    (7.0, 7.4),
];

fn fit_cbval(size: f64) -> f64 {
    let mut i = 0;
    while i + 2 < CBVALS.len() && (CBVALS[i].0 > size || CBVALS[i + 1].0 < size) {
        i += 1;
    }
    let (x1, y1) = CBVALS[i];
    let (x2, y2) = CBVALS[i + 1];
    (y2 - y1) * (size - x1) / (x2 - x1) + y1
}

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        // xorshift64*
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }

    fn below(&mut self, n: usize) -> usize {
        (((self.next() >> 32) * n as u64) >> 32) as usize
    }

    fn double(&mut self) -> f64 {
        (self.next() >> 11) as f64 / (1u64 << 53) as f64
    }
}

impl Solver {
    pub fn walk(&mut self) {
        let start = std::time::Instant::now();
        self.walk_untimed();
        self.stats.time_walk += start.elapsed().as_secs_f64();
    }

    /// Run local search and update the saved phases.  Must be called at
    /// the root level.
    fn walk_untimed(&mut self) {
        debug_assert_eq!(self.level, 0);
        self.stats.walks += 1;
        if self.opts.warmup {
            self.warmup();
        }
        let limit = self.effort_limit_from(self.last_walk_ticks, self.opts.walkeffort);
        self.last_walk_ticks = self.stats.search_ticks;
        // Collect clauses (root-false literals dropped, satisfied skipped).
        let mut lits: Vec<Lit> = Vec::new();
        let mut starts: Vec<u32> = vec![0];
        let mut push_clause = |solver: &Solver, clause: &mut dyn Iterator<Item = Lit>| {
            let start = lits.len();
            for l in clause {
                match solver.fixed(l) {
                    0 => lits.push(l),
                    v if v > 0 => {
                        lits.truncate(start);
                        return;
                    }
                    _ => {}
                }
            }
            if lits.len() == start {
                return;
            }
            starts.push(lits.len() as u32);
        };
        for idx in 0..self.watches.len() {
            let lit = Lit(idx as u32);
            for w in watch::iter(&self.watches[idx]) {
                if let Watch::Binary(other) = w
                    && lit < other
                {
                    push_clause(self, &mut [lit, other].into_iter());
                }
            }
        }
        let mut c = 0;
        while (c as usize) < self.arena.len() {
            let next = self.arena.next(c);
            if !self.arena.garbage(c) && !self.arena.redundant(c) {
                push_clause(self, &mut self.arena.lits(c).iter().copied());
            }
            c = next;
        }
        let clauses = starts.len() - 1;
        if clauses == 0 {
            return;
        }
        // Occurrence lists.
        let mut occs: Vec<Vec<u32>> = vec![Vec::new(); 2 * self.vars];
        for ci in 0..clauses {
            for &l in &lits[starts[ci] as usize..starts[ci + 1] as usize] {
                occs[l.idx()].push(ci as u32);
            }
        }
        // Initial assignment from the decision phases (target phases first
        // in stable mode), as Kissat's `import_decision_phases`.
        let mut value: Vec<bool> = (0..self.vars)
            .map(|v| {
                let pos = Lit::new(v as u32, false);
                match self.fixed(pos) {
                    0 => self.decide_phase(v as u32) > 0,
                    f => f > 0,
                }
            })
            .collect();
        let is_true = |value: &[bool], l: Lit| value[l.vidx()] != l.negated();
        let mut count: Vec<u32> = vec![0; clauses];
        let mut unsat: Vec<u32> = Vec::new();
        let mut pos: Vec<u32> = vec![u32::MAX; clauses];
        for ci in 0..clauses {
            let n = lits[starts[ci] as usize..starts[ci + 1] as usize]
                .iter()
                .filter(|&&l| is_true(&value, l))
                .count() as u32;
            count[ci] = n;
            if n == 0 {
                pos[ci] = unsat.len() as u32;
                unsat.push(ci as u32);
            }
        }
        // Break value table: cb^-break.
        let size = lits.len() as f64 / clauses as f64;
        let cb = if self.stats.walks & 1 != 0 {
            fit_cbval(size)
        } else {
            2.0
        };
        let base = 1.0 / cb;
        let mut table: Vec<f64> = Vec::new();
        let mut e = 1.0f64;
        while e > 0.0 && table.len() < 2048 {
            table.push(e);
            e *= base;
        }
        let epsilon = *table.last().unwrap();
        let mut rng = Rng(0x9e37_79b9_7f4a_7c15
            ^ self.stats.walks.wrapping_mul(0x1234_5678_9abc_def1)
            ^ self.opts.seed.wrapping_mul(0x2545_f491_4f6c_dd1d));
        // Best assignment: snapshot plus a prefix of the flip trail.
        let mut best_values = value.clone();
        let mut trail: Vec<u32> = Vec::new();
        let mut best_trail = 0usize;
        let mut minimum = unsat.len();
        let initial = minimum;
        let mut ticks = 0u64;
        let mut scores: Vec<f64> = Vec::new();
        let mut flips = 0u64;
        while !unsat.is_empty() && ticks < limit {
            if flips & 0xffff == 0 && self.terminated() {
                break;
            }
            flips += 1;
            let ci = unsat[rng.below(unsat.len())] as usize;
            let clause = &lits[starts[ci] as usize..starts[ci + 1] as usize];
            scores.clear();
            let mut sum = 0.0;
            for &l in clause {
                // Flipping l's variable breaks clauses where !l is the only
                // true literal.
                let mut breaks = 0usize;
                for &d in &occs[(!l).idx()] {
                    if count[d as usize] == 1 {
                        breaks += 1;
                    }
                }
                ticks += 1 + occs[(!l).idx()].len() as u64 / 8;
                let s = if breaks < table.len() {
                    table[breaks]
                } else {
                    epsilon
                };
                scores.push(s);
                sum += s;
            }
            let mut r = rng.double() * sum;
            let mut pick = clause[clause.len() - 1];
            for (k, &l) in clause.iter().enumerate() {
                if r < scores[k] {
                    pick = l;
                    break;
                }
                r -= scores[k];
            }
            // Flip: `pick` becomes true.
            value[pick.vidx()] = !pick.negated();
            for &d in &occs[pick.idx()] {
                let d = d as usize;
                count[d] += 1;
                if count[d] == 1 {
                    let p = pos[d] as usize;
                    let last = unsat.pop().unwrap();
                    if last as usize != d {
                        unsat[p] = last;
                        pos[last as usize] = p as u32;
                    }
                    pos[d] = u32::MAX;
                }
            }
            for &d in &occs[(!pick).idx()] {
                let d = d as usize;
                count[d] -= 1;
                if count[d] == 0 {
                    pos[d] = unsat.len() as u32;
                    unsat.push(d as u32);
                }
            }
            ticks += 1 + (occs[pick.idx()].len() + occs[(!pick).idx()].len()) as u64 / 8;
            trail.push(pick.var());
            if unsat.len() < minimum {
                minimum = unsat.len();
                if trail.len() > self.vars / 4 + 1000 {
                    best_values.copy_from_slice(&value);
                    trail.clear();
                }
                best_trail = trail.len();
            }
        }
        // Reconstruct the best assignment.
        for &v in &trail[..best_trail] {
            best_values[v as usize] = !best_values[v as usize];
        }
        self.stats.walk_flips += flips;
        self.stats.walk_ticks += ticks;
        if self.verbose(2) {
            println!(
                "c [walk-{}] {} flips, unsatisfied clauses {} -> {} of {}",
                self.stats.walks, flips, initial, minimum, clauses
            );
        }
        if minimum == initial {
            // No improvement: keep the saved phases.
            return;
        }
        for v in 0..self.vars {
            if self.flags[v] & ELIMINATED != 0 || self.fixed(Lit::new(v as u32, false)) != 0 {
                continue;
            }
            self.phases.saved[v] = if best_values[v] { 1 } else { -1 };
        }
    }
}
