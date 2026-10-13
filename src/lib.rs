//! crabsat: a CDCL SAT solver following the design of Kissat.

// Parallel per-variable arrays are naturally indexed by variable.
#![allow(clippy::needless_range_loop)]

mod analyze;
mod arena;
mod backtrack;
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

pub use incremental::{LearnFn, TerminateFn};
pub use options::Options;
pub use portfolio::PortfolioResult;
pub use proof::Proof;
pub use solver::Solver;
pub use stats::Stats;
pub use types::SolveResult;
