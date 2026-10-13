//! IPASIR C interface (`include/ipasir.h`).
//!
//! The functions follow the IPASIR specification: the solver starts in the
//! INPUT state, `ipasir_solve` returns 10 (SAT), 20 (UNSAT) or 0
//! (interrupted), `ipasir_val` is valid after SAT and `ipasir_failed` after
//! UNSAT.

use crate::{Callbacks, Options, SolveResult, Solver};
use std::ffi::{c_char, c_int, c_void};

/// Solver handle with the clause being added and the C callbacks.
pub struct IpasirSolver {
    solver: Solver,
    clause: Vec<i32>,
    callbacks: CCallbacks,
}

type TerminateFn = extern "C" fn(*mut c_void) -> c_int;
type LearnFn = extern "C" fn(*mut c_void, *mut i32);

#[derive(Default)]
struct CCallbacks {
    terminate: Option<(*mut c_void, TerminateFn)>,
    learn: Option<(*mut c_void, usize, LearnFn)>,
    buffer: Vec<i32>,
}

impl Callbacks for CCallbacks {
    fn terminate(&mut self) -> bool {
        self.terminate.is_some_and(|(state, f)| f(state) != 0)
    }

    fn learn_limit(&self) -> usize {
        self.learn.map_or(0, |(_, max_length, _)| max_length)
    }

    fn learn(&mut self, clause: &[i32]) {
        if let Some((state, _, f)) = self.learn {
            self.buffer.clear();
            self.buffer.extend_from_slice(clause);
            self.buffer.push(0);
            f(state, self.buffer.as_mut_ptr());
        }
    }
}

/// Name and version of the solver.
#[unsafe(no_mangle)]
pub extern "C" fn ipasir_signature() -> *const c_char {
    concat!("crabsat-", env!("CARGO_PKG_VERSION"), "\0")
        .as_ptr()
        .cast()
}

/// Create a new solver.
#[unsafe(no_mangle)]
pub extern "C" fn ipasir_init() -> *mut c_void {
    let opts = Options {
        incremental: true,
        quiet: true,
        ..Options::default()
    };
    Box::into_raw(Box::new(IpasirSolver {
        solver: Solver::new(opts),
        clause: Vec::new(),
        callbacks: CCallbacks::default(),
    }))
    .cast()
}

/// # Safety
/// `s` must be a pointer returned by `ipasir_init` and not yet released.
unsafe fn get<'a>(s: *mut c_void) -> &'a mut IpasirSolver {
    unsafe { &mut *s.cast::<IpasirSolver>() }
}

/// Release the solver.
///
/// # Safety
/// `s` must be a pointer returned by `ipasir_init`; it is invalid afterwards.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ipasir_release(s: *mut c_void) {
    drop(unsafe { Box::from_raw(s.cast::<IpasirSolver>()) });
}

/// Add a literal to the current clause, or finish it with 0.
///
/// # Safety
/// `s` must be a valid solver handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ipasir_add(s: *mut c_void, lit_or_zero: i32) {
    let s = unsafe { get(s) };
    if lit_or_zero == 0 {
        let clause = std::mem::take(&mut s.clause);
        s.solver.add_clause(&clause);
        s.clause = clause;
        s.clause.clear();
    } else {
        s.clause.push(lit_or_zero);
    }
}

/// Assume a literal for the next `ipasir_solve` call.
///
/// # Safety
/// `s` must be a valid solver handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ipasir_assume(s: *mut c_void, lit: i32) {
    unsafe { get(s) }.solver.assume(lit);
}

/// Solve under the current assumptions: 10 = SAT, 20 = UNSAT, 0 = interrupted.
///
/// # Safety
/// `s` must be a valid solver handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ipasir_solve(s: *mut c_void) -> c_int {
    let s = unsafe { get(s) };
    match s.solver.solve_with(&mut s.callbacks) {
        SolveResult::Sat => 10,
        SolveResult::Unsat => 20,
        SolveResult::Unknown => 0,
    }
}

/// Value of `lit` in the last model: `lit`, `-lit` or 0.
///
/// # Safety
/// `s` must be a valid solver handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ipasir_val(s: *mut c_void, lit: i32) -> i32 {
    unsafe { get(s) }.solver.val(lit)
}

/// Whether assumption `lit` was used to prove unsatisfiability.
///
/// # Safety
/// `s` must be a valid solver handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ipasir_failed(s: *mut c_void, lit: i32) -> c_int {
    unsafe { get(s) }.solver.failed(lit) as c_int
}

/// Set a callback polled during search; a non-zero result stops the search.
///
/// # Safety
/// `s` must be a valid solver handle; `state` is passed to `terminate`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ipasir_set_terminate(
    s: *mut c_void,
    state: *mut c_void,
    terminate: Option<extern "C" fn(*mut c_void) -> c_int>,
) {
    unsafe { get(s) }.callbacks.terminate = terminate.map(|f| (state, f));
}

/// Set a callback receiving learned clauses up to `max_length` literals
/// (zero-terminated DIMACS literals, valid during the call only).
///
/// # Safety
/// `s` must be a valid solver handle; `state` is passed to `learn`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ipasir_set_learn(
    s: *mut c_void,
    state: *mut c_void,
    max_length: c_int,
    learn: Option<extern "C" fn(*mut c_void, *mut i32)>,
) {
    unsafe { get(s) }.callbacks.learn = learn.map(|f| (state, max_length.max(0) as usize, f));
}
