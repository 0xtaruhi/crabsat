//! crabsat: a high-performance CDCL SAT solver following the design of
//! [Kissat](https://github.com/arminbiere/kissat), with an incremental
//! (IPASIR-style) interface.
//!
//! Literals are DIMACS integers: variable `v >= 1` is the literal `v`, its
//! negation is `-v`.
//!
//! ```
//! use crabsat::{Options, SolveResult, Solver};
//!
//! let mut solver = Solver::new(Options::default());
//! solver.add_clause(&[1, 2]);
//! solver.add_clause(&[-1, 2]);
//! assert_eq!(solver.solve(), SolveResult::Sat);
//! assert_eq!(solver.val(2), 2);
//!
//! // Assumptions hold for the next call only.
//! solver.assume(-2);
//! assert_eq!(solver.solve(), SolveResult::Unsat);
//! assert_eq!(solver.failed_assumptions().collect::<Vec<_>>(), vec![-2]);
//!
//! // Clauses can be added after solving.
//! solver.add_clause(&[-2, 3]);
//! assert_eq!(solver.solve(), SolveResult::Sat);
//! ```
//!
//! # Incremental and one-shot mode
//!
//! With the default options ([`Options::incremental`] is true) clauses and
//! assumptions may be added between calls.  Inprocessing stays enabled:
//! eliminated variables are reactivated when they are used again, and
//! [`Solver::freeze`] can protect variables that will be used later.  For a
//! single call on a fixed formula, `incremental: false` enables bounded
//! variable addition and saves memory; adding clauses with eliminated
//! variables after solving then panics.
//!
//! # Callbacks
//!
//! [`Solver::solve_with`] takes a [`Callbacks`] implementation for
//! termination checks and learned clauses; the callbacks may borrow local
//! data.  [`Solver::interrupter`] gives a handle that stops a running call
//! from another thread, and [`Solver::set_conflict_limit`] limits each
//! call.
//!
//! # Features
//!
//! - `compression` (default): [`dimacs::open`] reads gzip, bzip2, xz and
//!   lzma compressed files.

// Parallel per-variable arrays are naturally indexed by variable.
#![allow(clippy::needless_range_loop)]
#![warn(missing_docs)]

mod analyze;
mod arena;
mod backtrack;
mod clock;
mod compact;
mod congruence;
pub mod dimacs;
mod eliminate;
mod ema;
mod factor;
mod flags;
mod fxhash;
mod heap;
mod incremental;
pub mod ipasir;
mod kitten;
mod lucky;
mod options;
mod portfolio;
mod probe;
mod proof;
mod propagate;
mod queue;
mod reduce;
mod search;
mod share;
mod simplify;
mod solver;
mod stats;
mod sweep;
mod types;
mod walk;
mod watch;

pub use incremental::{Callbacks, Interrupter};
pub use options::Options;
pub use portfolio::PortfolioResult;
pub use proof::Proof;
pub use solver::Solver;
pub use stats::Stats;
pub use types::SolveResult;

/// The version of crabsat (`major.minor.patch`).
pub const VERSION: &str = env!("CARGO_PKG_VERSION");
