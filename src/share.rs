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
        self.replay_or_log(&new);
        let mut assigned = false;
        for ext in new {
            let Some(lit) = self.internal(ext) else {
                // Fixed and compacted away (consistent by construction).
                continue;
            };
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

/// Debugging aid: `CRABSAT_IMPORT_LOG=<prefix>` makes every portfolio
/// member write its imports to `<prefix>.<seed>`; `CRABSAT_REPLAY=<file>`
/// replays such a log in a single solver at the same search states.
impl Solver {
    fn replay_or_log(&mut self, units: &[Lit]) {
        if units.is_empty() {
            return;
        }
        if let Some(prefix) = std::env::var_os("CRABSAT_IMPORT_LOG") {
            use std::io::Write;
            let path = format!("{}.{}", prefix.to_string_lossy(), self.opts.seed);
            let mut f = std::fs::OpenOptions::new().create(true).append(true).open(path).unwrap();
            let lits: Vec<String> = units.iter().map(|l| l.to_dimacs().to_string()).collect();
            writeln!(f, "{} {} {}", self.stats.conflicts, self.stats.decisions, lits.join(" ")).unwrap();
        }
    }

    /// Import the logged units recorded at the current search state.
    pub fn replay_units(&mut self) -> bool {
        static PATH: std::sync::OnceLock<Option<std::ffi::OsString>> = std::sync::OnceLock::new();
        let Some(path) = PATH.get_or_init(|| std::env::var_os("CRABSAT_REPLAY")) else {
            return true;
        };
        if self.replay.is_none() {
            let text = std::fs::read_to_string(path).unwrap();
            let entries = text
                .lines()
                .map(|l| {
                    let v: Vec<i64> = l.split_whitespace().map(|x| x.parse().unwrap()).collect();
                    (v[0] as u64, v[1] as u64, v[2..].iter().map(|&d| Lit::from_dimacs(d as i32)).collect())
                })
                .collect();
            self.replay = Some(entries);
        }
        let entries = self.replay.as_mut().unwrap();
        let mut units = Vec::new();
        while let Some((c, d, _)) = entries.first() {
            if (*c, *d) != (self.stats.conflicts, self.stats.decisions) {
                break;
            }
            units.extend(entries.remove(0).2);
        }
        let mut assigned = false;
        for ext in units {
            let Some(lit) = self.internal(ext) else { continue };
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
        true
    }
}
