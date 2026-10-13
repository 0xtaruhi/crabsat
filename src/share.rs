//! Sharing of root-level units between portfolio solvers.
//!
//! Units on original variables are implied by the original formula, no
//! matter which (satisfiability preserving) simplifications a solver
//! performed, so they can be imported by every other solver unless the
//! variable was eliminated or substituted there.

use crate::solver::{ELIMINATED, Solver};
use crate::types::Lit;
use std::sync::Mutex;

/// A learned clause exported by a portfolio member (external literals).
#[derive(Clone)]
pub struct SharedClause {
    pub from: u32,
    pub glue: u32,
    pub lits: Vec<Lit>,
}

/// Bounded pool of shared clauses: entry `k` of the deque has global index
/// `base + k`.
#[derive(Default)]
struct ClausePool {
    base: usize,
    clauses: std::collections::VecDeque<SharedClause>,
}

const POOL_CAPACITY: usize = 1 << 20;

#[derive(Default)]
pub struct Shared {
    units: Mutex<Vec<Lit>>,
    clauses: Mutex<ClausePool>,
    /// Only variables below this index (original variables) are shared.
    pub vars: usize,
}

impl Shared {
    pub(crate) fn new(vars: usize) -> Shared {
        Shared {
            vars,
            ..Default::default()
        }
    }
}

impl Solver {
    /// Remember a learned clause for export (if short with small glue and
    /// only on original variables).
    pub(crate) fn export_clause(&mut self, lits: &[Lit], glue: u32) {
        let Some(shared) = self.shared.as_ref() else {
            return;
        };
        if lits.len() > self.opts.sharesize as usize || glue > self.opts.shareglue {
            return;
        }
        let mut ext = Vec::with_capacity(lits.len());
        for &l in lits {
            let e = self.external(l);
            if e.vidx() >= shared.vars {
                return;
            }
            ext.push(e);
        }
        self.export_buffer.push(SharedClause {
            from: self.share_id,
            glue,
            lits: ext,
        });
    }

    /// Exchange learned clauses (called at restarts).  Imported clauses are
    /// added at the root level.  Returns false on inconsistency.
    pub(crate) fn share_clauses(&mut self) -> bool {
        let Some(shared) = self.shared.clone() else {
            return true;
        };
        if !self.opts.share || self.stats.conflicts < self.last_share + self.opts.shareint {
            return true;
        }
        self.last_share = self.stats.conflicts;
        let mut new: Vec<SharedClause> = Vec::new();
        {
            let mut pool = shared.clauses.lock().unwrap();
            for c in self.export_buffer.drain(..) {
                pool.clauses.push_back(c);
                if pool.clauses.len() > POOL_CAPACITY {
                    pool.clauses.pop_front();
                    pool.base += 1;
                }
            }
            let start = self.imported_clauses.max(pool.base);
            for k in start - pool.base..pool.clauses.len() {
                let c = &pool.clauses[k];
                if c.from != self.share_id {
                    new.push(SharedClause {
                        from: c.from,
                        glue: c.glue,
                        lits: c.lits.clone(),
                    });
                }
            }
            self.imported_clauses = pool.base + pool.clauses.len();
        }
        if new.is_empty() {
            return true;
        }
        if self.level > 0 {
            self.backtrack_in_consistent_state(0);
        }
        let mut lits: Vec<Lit> = Vec::new();
        'clauses: for c in new {
            lits.clear();
            for &e in &c.lits {
                match self.internal(e) {
                    Some(l) => {
                        if self.flags[l.vidx()].has(ELIMINATED) {
                            continue 'clauses;
                        }
                        match self.fixed(l) {
                            0 => lits.push(l),
                            v if v > 0 => continue 'clauses,
                            _ => {}
                        }
                    }
                    None => {
                        let v = self.ext_fixed[e.vidx()];
                        if v == 0 {
                            continue 'clauses; // eliminated
                        }
                        if (v > 0) != e.negated() {
                            continue 'clauses; // satisfied
                        }
                    }
                }
            }
            // The root level is fully propagated, so no literal is assigned
            // at this point unless it was fixed (handled above).
            if lits.iter().any(|&l| self.value(l) != 0) {
                continue;
            }
            self.stats.imported_clauses += 1;
            match lits.len() {
                0 => {
                    self.mark_inconsistent();
                    return false;
                }
                1 => self.assign_unit(lits[0]),
                2 => self.new_binary(lits[0], lits[1]),
                _ => {
                    self.new_large(&lits, true, c.glue);
                }
            }
        }
        if self.propagate().is_some() {
            self.mark_inconsistent();
            return false;
        }
        true
    }

    /// Export new root-level units and import those of other solvers.
    /// Must be called at level 0 after propagation.  Returns false if the
    /// formula became inconsistent.
    pub(crate) fn share_units(&mut self) -> bool {
        let Some(shared) = self.shared.clone() else {
            return true;
        };
        debug_assert_eq!(self.level, 0);
        let mut units = shared.units.lock().unwrap();
        // Units are exchanged as external literals.
        while self.exported < self.trail.len() {
            let lit = self.external(self.trail[self.exported]);
            self.exported += 1;
            if lit.vidx() < shared.vars {
                units.push(lit);
            }
        }
        let new: Vec<Lit> = units[self.imported.min(units.len())..].to_vec();
        self.imported = units.len();
        drop(units);
        let mut assigned = false;
        for ext in new {
            let Some(lit) = self.internal(ext) else {
                // Fixed and compacted away (consistent by construction).
                continue;
            };
            if self.flags[lit.vidx()].has(ELIMINATED) {
                continue;
            }
            match self.value(lit) {
                0 => {
                    self.assign_unit(lit);
                    self.stats.imported_units += 1;
                    assigned = true;
                }
                v if v < 0 => {
                    self.mark_inconsistent();
                    return false;
                }
                _ => {}
            }
        }
        if assigned && self.propagate().is_some() {
            self.mark_inconsistent();
            return false;
        }
        // Units derived by propagation are exported next time.
        true
    }
}
