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
use crate::types::{Lit, SolveResult, Var};
use std::ptr::NonNull;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

use crate::flags::FROZEN;

/// Callbacks invoked during [`Solver::solve_with`].  All methods have
/// defaults, so an implementation only overrides what it needs; `()`
/// implements the trait with no callbacks.
pub trait Callbacks {
    /// Polled regularly during the search; returning true stops the call
    /// with [`SolveResult::Unknown`](crate::SolveResult::Unknown).
    fn terminate(&mut self) -> bool {
        false
    }

    /// Learned clauses with at most this many literals are passed to
    /// [`Callbacks::learn`] (0 disables it).
    fn learn_limit(&self) -> usize {
        0
    }

    /// Receives a learned clause (DIMACS literals).
    fn learn(&mut self, _clause: &[i32]) {}
}

impl Callbacks for () {}

/// The callbacks of the running `solve_with` call, with their lifetime
/// erased.  Only set (and only dereferenced) during that call.
#[derive(Clone, Copy)]
pub(crate) struct CallbacksPtr(NonNull<dyn Callbacks>);

// SAFETY: the pointer is only dereferenced during the `solve_with` call that
// stored it, on the thread running that call (which holds the exclusive
// borrow of the callbacks); a `Solver` can only move between threads
// outside of such a call.
unsafe impl Send for CallbacksPtr {}

/// A handle to interrupt a solver from another thread (see
/// [`Solver::interrupter`]).
#[derive(Clone, Debug)]
pub struct Interrupter(pub(crate) Arc<AtomicBool>);

impl Interrupter {
    /// Stop the running solve call (or the next one if none is running);
    /// it returns [`SolveResult::Unknown`](crate::SolveResult::Unknown).
    pub fn interrupt(&self) {
        self.0.store(true, Ordering::Relaxed);
    }
}

/// State of the incremental interface.
#[derive(Default)]
pub struct Incremental {
    /// Assumptions (external literals) for the next solve call.
    pub assumptions: Vec<Lit>,
    /// Failed assumptions of the last unsatisfiable call.
    pub failed: Vec<Lit>,
    /// Model of the last satisfiable call.
    pub model: Vec<i32>,
    pub callbacks: Option<CallbacksPtr>,
    /// Cached `learn_limit` of the current callbacks.
    pub learn_limit: usize,
    pub terminate_calls: std::cell::Cell<u32>,
    /// User interrupt flag (reset after the call it stopped).
    pub interrupt: Option<Arc<AtomicBool>>,
    /// Forced phases of external variables (1, -1 or 0 = none).
    pub forced: Vec<i8>,
    pub any_forced: bool,
    /// Freeze counts of external variables.
    pub frozen: Vec<u32>,
}

impl Solver {
    /// Add an assumption (DIMACS literal) for the next `solve` call.
    pub fn assume(&mut self, d: i32) {
        let e = dimacs_lit(d);
        self.prepare_external(e.vidx());
        self.incremental.assumptions.push(e);
    }

    /// Whether the assumption `d` was used to derive unsatisfiability in the
    /// last `solve` call.
    pub fn failed(&self, d: i32) -> bool {
        let e = dimacs_lit(d);
        self.incremental.failed.contains(&e)
    }

    /// Value of a literal in the model of the last satisfiable `solve` call:
    /// `d` if true, `-d` if false, `0` if unknown.
    pub fn val(&self, d: i32) -> i32 {
        let v = dimacs_lit(d).vidx();
        match self.incremental.model.get(v) {
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
        match self.ext.e2i[e] {
            Lit::INVALID => self.ext.fixed[e] == 0,
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
        let ext = std::mem::take(&mut self.ext.extension);
        let mut groups: Vec<(usize, usize)> = Vec::new();
        let mut start = 0;
        for k in 1..=ext.len() {
            if k == ext.len() || ext[k] & WITNESS != 0 {
                groups.push((start, k));
                start = k;
            }
        }
        let mut reactivated = vec![false; self.ext.vars];
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
        self.ext.extension = kept;
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
        match self.ext.e2i[e] {
            Lit::INVALID => {
                // Compacted away: allocate a new internal variable.
                let v = self.vars;
                self.grow_internal(v + 1);
                self.ext.e2i[e] = Lit::new(v as Var, false);
                self.ext.i2e.push(e as u32);
                if self.frozen_external(e) {
                    self.flags[v].insert(FROZEN);
                }
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
        self.incremental.failed.clear();
        for k in 0..self.incremental.assumptions.len() {
            if let Some(l) = self.internal(self.incremental.assumptions[k]) {
                self.flags[l.vidx()].insert(FROZEN);
            }
        }
    }

    pub(crate) fn end_assumptions(&mut self) {
        for k in 0..self.incremental.assumptions.len() {
            let e = self.incremental.assumptions[k];
            if self.frozen_external(e.vidx()) {
                continue;
            }
            if let Some(l) = self.internal(e) {
                self.flags[l.vidx()].remove(FROZEN);
            }
        }
        self.incremental.assumptions.clear();
    }

    /// Decide the next assumption if not all of them are decided.  Returns
    /// `Some(true)` if a decision (or pseudo decision) was made, `Some(false)`
    /// if an assumption is falsified (failed assumptions are computed) and
    /// `None` if all assumptions are decided.
    pub(crate) fn decide_assumption(&mut self) -> Option<bool> {
        let level = self.level as usize;
        if level >= self.incremental.assumptions.len() {
            return None;
        }
        let e = self.incremental.assumptions[level];
        let lit = match self.internal(e) {
            Some(l) => l,
            None => {
                // Fixed at the root and compacted away.
                let v = self.ext.fixed[e.vidx()];
                if (v > 0) != e.negated() {
                    self.pseudo_decision(Lit::INVALID);
                    return Some(true);
                }
                self.incremental.failed = vec![e];
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
        self.incremental.failed = failed;
    }

    /// Solve under the current assumptions, calling `callbacks` during the
    /// search.  The assumptions are cleared afterwards.
    pub fn solve_with<C: Callbacks>(&mut self, callbacks: &mut C) -> SolveResult {
        let ptr: NonNull<dyn Callbacks + '_> = NonNull::from(callbacks as &mut dyn Callbacks);
        // SAFETY: only the lifetime is erased; the pointer is removed before
        // this function returns and is not used after that (it is
        // overwritten at the start of every call).
        let ptr: NonNull<dyn Callbacks> = unsafe { std::mem::transmute(ptr) };
        self.incremental.callbacks = Some(CallbacksPtr(ptr));
        self.incremental.learn_limit = unsafe { ptr.as_ref() }.learn_limit();
        self.incremental.terminate_calls.set(0);
        let res = self.solve_internal();
        self.incremental.callbacks = None;
        res
    }

    /// A handle to interrupt this solver from another thread.
    pub fn interrupter(&mut self) -> Interrupter {
        Interrupter(
            self.incremental
                .interrupt
                .get_or_insert_with(|| Arc::new(AtomicBool::new(false)))
                .clone(),
        )
    }

    /// The failed assumptions of the last unsatisfiable call: a subset of
    /// the assumptions which is unsatisfiable together with the clauses
    /// (empty if the clauses alone are unsatisfiable).
    pub fn failed_assumptions(&self) -> impl Iterator<Item = i32> + '_ {
        self.incremental.failed.iter().map(|l| l.to_dimacs())
    }

    /// Prefer the phase of `lit` when deciding its variable.
    pub fn phase(&mut self, lit: i32) {
        let e = dimacs_lit(lit);
        self.reserve_vars(e.vidx() + 1);
        if self.incremental.forced.len() < self.ext.vars {
            self.incremental.forced.resize(self.ext.vars, 0);
        }
        self.incremental.forced[e.vidx()] = if e.negated() { -1 } else { 1 };
        self.incremental.any_forced = true;
    }

    /// Undo [`Solver::phase`] for variable `var`.
    pub fn unphase(&mut self, var: i32) {
        let e = dimacs_lit(var).vidx();
        if let Some(f) = self.incremental.forced.get_mut(e) {
            *f = 0;
        }
    }

    /// Forced phase of internal variable `v` (0 if none).
    #[inline]
    pub(crate) fn forced_phase(&self, v: Var) -> i8 {
        let e = self.ext.i2e[v as usize] as usize;
        self.incremental.forced.get(e).copied().unwrap_or(0)
    }

    /// Protect variable `var` from elimination and substitution until it
    /// is melted as often as it was frozen.  (Not needed for correctness:
    /// eliminated variables are reactivated when used again, which is more
    /// expensive.)
    pub fn freeze(&mut self, var: i32) {
        let e = dimacs_lit(var).vidx();
        self.prepare_external(e);
        if self.incremental.frozen.len() < self.ext.vars {
            self.incremental.frozen.resize(self.ext.vars, 0);
        }
        self.incremental.frozen[e] += 1;
        if let Some(l) = self.internal(Lit::new(e as Var, false)) {
            self.flags[l.vidx()].insert(FROZEN);
        }
    }

    /// Undo one [`Solver::freeze`] of variable `var`.
    pub fn melt(&mut self, var: i32) {
        let e = dimacs_lit(var).vidx();
        let Some(count) = self.incremental.frozen.get_mut(e) else {
            return;
        };
        if *count == 0 {
            return;
        }
        *count -= 1;
        if *count == 0 {
            if let Some(l) = self.internal(Lit::new(e as Var, false)) {
                self.flags[l.vidx()].remove(FROZEN);
            }
        }
    }

    /// Whether variable `var` is frozen.
    pub fn is_frozen(&self, var: i32) -> bool {
        let e = dimacs_lit(var).vidx();
        self.incremental.frozen.get(e).is_some_and(|&c| c > 0)
    }

    fn frozen_external(&self, e: usize) -> bool {
        self.incremental.frozen.get(e).is_some_and(|&c| c > 0)
    }

    /// Whether the search must stop: interrupted, or the termination
    /// callback (polled about every 64 checks) says so.
    pub(crate) fn interrupted(&self) -> bool {
        if self
            .incremental
            .interrupt
            .as_ref()
            .is_some_and(|f| f.load(Ordering::Relaxed))
        {
            return true;
        }
        let Some(cb) = self.incremental.callbacks else {
            return false;
        };
        let n = self.incremental.terminate_calls.get();
        self.incremental.terminate_calls.set(n.wrapping_add(1));
        // SAFETY: set by the running `solve_with` call (see `CallbacksPtr`);
        // the callbacks are not otherwise accessed during the call.
        n.is_multiple_of(64) && unsafe { (*cb.0.as_ptr()).terminate() }
    }

    /// Report the learned clause `lits` to the learn callback.
    pub(crate) fn learn_callback(&mut self, lits: &[Lit]) {
        if lits.len() > self.incremental.learn_limit {
            return;
        }
        let Some(cb) = self.incremental.callbacks else {
            return;
        };
        let clause: Vec<i32> = lits.iter().map(|&l| self.external(l).to_dimacs()).collect();
        // SAFETY: as in `interrupted`.
        unsafe { (*cb.0.as_ptr()).learn(&clause) };
    }
}

/// Convert a DIMACS literal, rejecting 0.
pub(crate) fn dimacs_lit(d: i32) -> Lit {
    assert!(d != 0 && d != i32::MIN, "invalid literal {d}");
    Lit::from_dimacs(d)
}
