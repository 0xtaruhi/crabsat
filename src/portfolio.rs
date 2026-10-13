//! Parallel portfolio: diversified solvers on the same formula, sharing
//! units and short learned clauses (see `share.rs`); the first result wins.

use crate::share::Shared;
use crate::{Options, SolveResult, Solver};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};

/// Result of [`Solver::solve_portfolio`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PortfolioResult {
    /// The result of the winning member.
    pub result: SolveResult,
    /// Model (DIMACS literals of all variables) if satisfiable.
    pub model: Vec<i32>,
    /// Index of the member which found the result (0 is `self`).
    pub winner: usize,
}

/// Options of portfolio member `i` (member 0 uses the given options).
fn diversify(base: &Options, i: usize) -> Options {
    let mut o = base.clone();
    o.seed = i as u64;
    o.quiet = true;
    o.verbose = 0;
    o.check = false;
    if base.portfolio == 1 {
        match i % 8 {
            1 => o.stable = 2,
            2 => o.phase = false,
            3 => o.target = 2,
            4 => {
                o.stable = 2;
                o.phase = false;
            }
            5 => o.walkeffort = 150,
            6 => {
                o.randec = false;
                o.reorder = 0;
            }
            7 => o.stable = 0,
            _ => {}
        }
        return o;
    }
    match i % 8 {
        1 => o.stable = 2,
        2 => o.stable = 0,
        3 => o.phase = false,
        4 => o.target = 2,
        5 => o.chrono = false,
        6 => {
            o.stable = 2;
            o.phase = false;
        }
        7 => o.tier2 = 8,
        _ => {}
    }
    o
}

impl Solver {
    /// Solve with `threads` diversified solvers: `self` and `threads - 1`
    /// new solvers built from `clauses`, which must be the clauses added to
    /// `self`.  The conflict limit of `self` applies to all members, and an
    /// interrupt of `self` stops all of them.
    pub fn solve_portfolio(&mut self, clauses: &[Vec<i32>], threads: usize) -> PortfolioResult {
        let vars = self.ext.vars;
        let flag = self
            .terminate
            .get_or_insert_with(|| Arc::new(AtomicBool::new(false)))
            .clone();
        let conflicts = self.limits.conflicts;
        let base = self.opts.clone();
        let shared = Arc::new(Shared::new(vars));
        let result: Mutex<Option<PortfolioResult>> = Mutex::new(None);
        let finish = |result_: SolveResult, model: Vec<i32>, winner: usize| {
            if result_ == SolveResult::Unknown {
                return;
            }
            let mut r = result.lock().unwrap();
            if r.is_none() {
                *r = Some(PortfolioResult {
                    result: result_,
                    model,
                    winner,
                });
                flag.store(true, Ordering::Relaxed);
            }
        };
        let solve = |s: &mut Solver| {
            let res = s.solve();
            let model = s.model().to_vec();
            (res, model)
        };
        self.sharing.pool = Some(shared.clone());
        // Every member preprocesses with its own options: this is done in
        // parallel and diversifies the simplified formulas (cloning a single
        // preprocessed solver was measured to be worse).
        std::thread::scope(|scope| {
            for i in 1..threads {
                let shared = shared.clone();
                let flag = flag.clone();
                let (finish, solve, base) = (&finish, &solve, &base);
                scope.spawn(move || {
                    let mut s = Solver::new(diversify(base, i));
                    s.sharing.id = i as u32;
                    s.reserve_vars(vars);
                    for c in clauses {
                        s.add_clause(c);
                    }
                    s.terminate = Some(flag);
                    s.sharing.pool = Some(shared);
                    s.limits.conflicts = conflicts;
                    let (res, model) = solve(&mut s);
                    finish(res, model, i);
                });
            }
            let (res, model) = solve(self);
            finish(res, model, 0);
            if res == SolveResult::Unknown {
                // Limit reached: let the others stop too.
                flag.store(true, Ordering::Relaxed);
            }
        });
        self.sharing.pool = None;
        self.terminate = None;
        result.into_inner().unwrap().unwrap_or(PortfolioResult {
            result: SolveResult::Unknown,
            model: Vec::new(),
            winner: 0,
        })
    }
}
