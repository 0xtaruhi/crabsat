//! Incremental solving: assumptions, failed assumptions, adding clauses
//! after solving and reactivation of eliminated variables.
//!
//! Assumptions are decided first, one per decision level (levels of
//! assumptions which are already true are "pseudo levels" without an
//! assignment).  Variables of assumptions are frozen during a solve call so
//! that inprocessing does not eliminate or substitute them.
//!
//! When a clause or an assumption mentions a variable which was eliminated
//! (by variable elimination or substitution), the clauses saved on the
//! extension stack for it are added back to the formula and the variable
//! becomes active again (as in CaDiCaL).  This requires the extension stack
//! to contain all removed clauses, which is guaranteed in incremental mode
//! (see `Options::incremental`).

use crate::solver::{DECISION_REASON, ELIMINATE, ELIMINATED, Frame, SUBSUME, Solver, WITNESS};
use crate::types::{Lit, Var};

use crate::flags::FROZEN;

/// Callback polled during search; returning true stops the search.
pub type TerminateFn = Box<dyn Fn() -> bool + Send>;
/// Callback receiving learned clauses (DIMACS literals).
pub type LearnFn = Box<dyn FnMut(&[i32]) + Send>;

impl Solver {
    /// Add an assumption (DIMACS literal) for the next `solve` call.
    pub fn assume(&mut self, d: i32) {
        let e = Lit::from_dimacs(d);
        self.prepare_external(e.vidx());
        self.assumptions.push(e);
    }

    /// Whether the assumption `d` was used to derive unsatisfiability in the
    /// last `solve` call.
    pub fn failed(&self, d: i32) -> bool {
        let e = Lit::from_dimacs(d);
        self.failed_assumptions.contains(&e)
    }

    /// Value of a literal in the model of the last satisfiable `solve` call:
    /// `d` if true, `-d` if false, `0` if unknown.
    pub fn val(&self, d: i32) -> i32 {
        let v = d.unsigned_abs() as usize - 1;
        match self.last_model.get(v) {
            Some(&m) if (m > 0) == (d > 0) => d,
            Some(_) => -d,
            None => 0,
        }
    }

    /// Make sure the external variable exists and is active (reactivating
    /// it if it was eliminated) and the solver is back at the root level.
    pub(crate) fn prepare_external(&mut self, e: usize) {
        if self.level > 0 {
            self.backtrack_without_updating_phases(0);
        }
        self.reserve_vars(e + 1);
        if self.is_eliminated_external(e) {
            self.reactivate(e);
        }
    }

    fn is_eliminated_external(&self, e: usize) -> bool {
        match self.e2i[e] {
            Lit::INVALID => self.ext_fixed[e] == 0,
            i => self.flags[i.vidx()].has(ELIMINATED),
        }
    }

    /// Restore all extension stack clauses needed to make external variable
    /// `e` active again (transitively for other eliminated variables in
    /// those clauses).
    fn reactivate(&mut self, e: usize) {
        assert!(
            self.opts.incremental,
            "eliminated variable {} used again (requires incremental mode)",
            e + 1
        );
        // Split the extension stack into groups [witness, literals...].
        let ext = std::mem::take(&mut self.extension);
        let mut groups: Vec<(usize, usize)> = Vec::new();
        let mut start = 0;
        for k in 1..=ext.len() {
            if k == ext.len() || ext[k] & WITNESS != 0 {
                groups.push((start, k));
                start = k;
            }
        }
        let mut reactivated = vec![false; self.evars];
        let mut restored = vec![false; groups.len()];
        let mut work = vec![e];
        reactivated[e] = true;
        while let Some(x) = work.pop() {
            for (g, &(s, t)) in groups.iter().enumerate() {
                if restored[g] {
                    continue;
                }
                if !ext[s..t].iter().any(|&l| (Lit(l & !WITNESS)).vidx() == x) {
                    continue;
                }
                restored[g] = true;
                for &l in &ext[s..t] {
                    let y = Lit(l & !WITNESS).vidx();
                    if !reactivated[y] && self.is_eliminated_external(y) {
                        reactivated[y] = true;
                        work.push(y);
                    }
                }
            }
        }
        let mut kept = Vec::with_capacity(ext.len());
        let mut clauses: Vec<Vec<i32>> = Vec::new();
        for (g, &(s, t)) in groups.iter().enumerate() {
            if restored[g] {
                clauses.push(
                    ext[s..t]
                        .iter()
                        .map(|&l| Lit(l & !WITNESS).to_dimacs())
                        .collect(),
                );
            } else {
                kept.extend_from_slice(&ext[s..t]);
            }
        }
        self.extension = kept;
        for (y, &r) in reactivated.iter().enumerate() {
            if r {
                self.activate_external(y);
            }
        }
        self.stats.reactivated += reactivated.iter().filter(|&&r| r).count() as u64;
        for c in clauses {
            self.add_clause(&c);
        }
    }

    fn activate_external(&mut self, e: usize) {
        match self.e2i[e] {
            Lit::INVALID => {
                // Compacted away: allocate a new internal variable.
                let v = self.vars;
                self.grow_internal(v + 1);
                self.e2i[e] = Lit::new(v as Var, false);
                self.i2e.push(e as u32);
                if let Some(p) = self.proof.as_mut() {
                    p.map.push(e as u32);
                }
            }
            i => {
                let v = i.var();
                let f = &mut self.flags[v as usize];
                if !f.has(ELIMINATED) {
                    return;
                }
                f.remove(ELIMINATED);
                f.insert(ELIMINATE | SUBSUME);
                self.eliminated -= 1;
                self.unassigned += 1;
                self.queue.enqueue(v, true);
                if !self.heap.contains(v) {
                    self.heap.push(v);
                }
            }
        }
    }

    /// Map the external assumptions and freeze their variables.
    pub(crate) fn start_assumptions(&mut self) {
        self.failed_assumptions.clear();
        for k in 0..self.assumptions.len() {
            if let Some(l) = self.internal(self.assumptions[k]) {
                self.flags[l.vidx()].insert(FROZEN);
            }
        }
    }

    pub(crate) fn end_assumptions(&mut self) {
        for k in 0..self.assumptions.len() {
            if let Some(l) = self.internal(self.assumptions[k]) {
                self.flags[l.vidx()].remove(FROZEN);
            }
        }
        self.assumptions.clear();
    }

    /// Decide the next assumption if not all of them are decided.  Returns
    /// `Some(true)` if a decision (or pseudo decision) was made, `Some(false)`
    /// if an assumption is falsified (failed assumptions are computed) and
    /// `None` if all assumptions are decided.
    pub(crate) fn decide_assumption(&mut self) -> Option<bool> {
        let level = self.level as usize;
        if level >= self.assumptions.len() {
            return None;
        }
        let e = self.assumptions[level];
        let lit = match self.internal(e) {
            Some(l) => l,
            None => {
                // Fixed at the root and compacted away.
                let v = self.ext_fixed[e.vidx()];
                if (v > 0) != e.negated() {
                    self.pseudo_decision(Lit::INVALID);
                    return Some(true);
                }
                self.failed_assumptions = vec![e];
                return Some(false);
            }
        };
        match self.value(lit) {
            0 => {
                self.stats.decisions += 1;
                self.assign_decision(lit);
                Some(true)
            }
            v if v > 0 => {
                self.pseudo_decision(lit);
                Some(true)
            }
            _ => {
                self.analyze_failed_assumption(e, lit);
                Some(false)
            }
        }
    }

    /// Open a decision level without assignment (assumption already true).
    fn pseudo_decision(&mut self, lit: Lit) {
        self.level += 1;
        self.frames.push(Frame {
            decision: if lit == Lit::INVALID { Lit(0) } else { lit },
            trail: self.trail.len() as u32,
            used: 0,
            promote: false,
        });
    }

    /// The assumption `e` (internal `lit`) is false: collect the
    /// assumptions (decisions) it depends on.
    fn analyze_failed_assumption(&mut self, e: Lit, lit: Lit) {
        let mut failed = vec![e];
        let mut seen = vec![false; self.vars];
        let mut stack = vec![(!lit).var()];
        seen[(!lit).vidx()] = true;
        while let Some(v) = stack.pop() {
            let a = self.assigned[v as usize];
            if a.level == 0 {
                continue;
            }
            if a.reason == DECISION_REASON {
                let d = if self.values[2 * v as usize] > 0 {
                    Lit::new(v, false)
                } else {
                    Lit::new(v, true)
                };
                failed.push(self.external(d));
                continue;
            }
            let reasons: Vec<Lit> = if a.has(crate::solver::BINARY) {
                vec![Lit(a.reason)]
            } else {
                self.arena.lits(a.reason).to_vec()
            };
            for r in reasons {
                if !seen[r.vidx()] {
                    seen[r.vidx()] = true;
                    stack.push(r.var());
                }
            }
        }
        failed.sort_unstable();
        failed.dedup();
        self.failed_assumptions = failed;
    }

    /// Set a callback polled during search (about every 64 checks);
    /// returning true stops the search with `SolveResult::Unknown`.
    pub fn set_terminate(&mut self, callback: Option<TerminateFn>) {
        self.terminate_cb = callback;
    }

    /// Set a callback receiving every learned clause with at most
    /// `max_length` literals.
    pub fn set_learn(&mut self, max_length: usize, callback: Option<LearnFn>) {
        self.learn_cb = callback.map(|f| (max_length, f));
    }

    /// Call the termination callback (throttled).
    pub(crate) fn terminate_callback(&self) -> bool {
        let Some(cb) = &self.terminate_cb else {
            return false;
        };
        let n = self.terminate_calls.get().wrapping_add(1);
        self.terminate_calls.set(n);
        n % 64 == 1 && cb()
    }

    /// Report the learned clause `lits` to the learn callback.
    pub(crate) fn learn_callback(&mut self, lits: &[Lit]) {
        let Some((max_length, _)) = self.learn_cb else {
            return;
        };
        if lits.len() > max_length {
            return;
        }
        let clause: Vec<i32> = lits.iter().map(|&l| self.external(l).to_dimacs()).collect();
        if let Some((_, f)) = self.learn_cb.as_mut() {
            f(&clause);
        }
    }
}
