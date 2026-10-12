//! Sharing of root-level units between portfolio solvers.
//!
//! Units on original variables are implied by the original formula, no
//! matter which (satisfiability preserving) simplifications a solver
//! performed, so they can be imported by every other solver unless the
//! variable was eliminated or substituted there.

use crate::solver::{Solver, ELIMINATED};
use crate::types::Lit;
use std::sync::Mutex;

#[derive(Default)]
pub struct Shared {
    units: Mutex<Vec<Lit>>,
    /// Only variables below this index (original variables) are shared.
    pub vars: usize,
}

impl Shared {
    pub fn new(vars: usize) -> Shared {
        Shared { units: Mutex::new(Vec::new()), vars }
    }
}

impl Solver {
    /// Export new root-level units and import those of other solvers.
    /// Must be called at level 0 after propagation.  Returns false if the
    /// formula became inconsistent.
    pub fn share_units(&mut self) -> bool {
        let Some(shared) = self.shared.clone() else { return true };
        debug_assert_eq!(self.level, 0);
        let mut units = shared.units.lock().unwrap();
        while self.exported < self.trail.len() {
            let lit = self.trail[self.exported];
            self.exported += 1;
            if lit.vidx() < shared.vars {
                units.push(lit);
            }
        }
        let new: Vec<Lit> = units[self.imported.min(units.len())..].to_vec();
        self.imported = units.len();
        drop(units);
        let mut assigned = false;
        for lit in new {
            if self.flags[lit.vidx()] & ELIMINATED != 0 {
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
