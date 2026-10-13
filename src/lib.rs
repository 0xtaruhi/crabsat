//! crabsat: a CDCL SAT solver following the design of Kissat.

// Parallel per-variable arrays are naturally indexed by variable.
#![allow(clippy::needless_range_loop, clippy::chunks_exact_to_as_chunks)]

pub mod analyze;
pub mod arena;
pub mod backtrack;
pub mod compact;
pub mod congruence;
pub mod dimacs;
pub mod eliminate;
pub mod ema;
pub mod factor;
pub mod fxhash;
pub mod heap;
pub mod incremental;
pub mod ipasir;
pub mod kitten;
pub mod lucky;
pub mod options;
pub mod probe;
pub mod proof;
pub mod propagate;
pub mod queue;
pub mod reduce;
pub mod search;
pub mod share;
pub mod simplify;
pub mod solver;
pub mod stats;
pub mod sweep;
pub mod types;
pub mod walk;
pub mod watch;

pub use options::Options;
pub use solver::Solver;
pub use types::{Lit, SolveResult};
