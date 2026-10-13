//! Basic literal and variable types.
//!
//! Literals are encoded as in Kissat: `2 * var + sign`, so negation is a
//! single XOR and literal-indexed arrays place both polarities next to each
//! other.

use std::fmt;
use std::ops::Not;

/// Internal variable index (0-based).
pub type Var = u32;

/// Internal literal: `2 * var + negated`.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
#[repr(transparent)]
pub struct Lit(pub u32);

impl Lit {
    pub const INVALID: Lit = Lit(u32::MAX);

    #[inline(always)]
    pub fn new(var: Var, negated: bool) -> Lit {
        Lit(var << 1 | negated as u32)
    }

    #[inline(always)]
    pub fn var(self) -> Var {
        self.0 >> 1
    }

    /// Index into literal-indexed arrays.
    #[inline(always)]
    pub fn idx(self) -> usize {
        self.0 as usize
    }

    /// Index into variable-indexed arrays.
    #[inline(always)]
    pub fn vidx(self) -> usize {
        (self.0 >> 1) as usize
    }

    #[inline(always)]
    pub fn negated(self) -> bool {
        self.0 & 1 != 0
    }

    /// Convert a non-zero DIMACS literal.
    #[inline]
    pub fn from_dimacs(d: i32) -> Lit {
        debug_assert!(d != 0);
        Lit::new(d.unsigned_abs() - 1, d < 0)
    }

    #[inline]
    pub fn to_dimacs(self) -> i32 {
        let v = self.var() as i32 + 1;
        if self.negated() { -v } else { v }
    }
}

impl Not for Lit {
    type Output = Lit;
    #[inline(always)]
    fn not(self) -> Lit {
        Lit(self.0 ^ 1)
    }
}

impl fmt::Debug for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if *self == Lit::INVALID {
            write!(f, "<invalid>")
        } else {
            write!(f, "{}", self.to_dimacs())
        }
    }
}

impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

/// Result of a solver call.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum SolveResult {
    /// Satisfiable (a model is available).
    Sat,
    /// Unsatisfiable (under the assumptions, if any).
    Unsat,
    /// Stopped by a limit, an interrupt or the termination callback.
    Unknown,
}

impl SolveResult {
    /// SAT competition exit code.
    pub fn exit_code(self) -> i32 {
        match self {
            SolveResult::Sat => 10,
            SolveResult::Unsat => 20,
            SolveResult::Unknown => 0,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dimacs_roundtrip() {
        for d in [1, -1, 2, -2, 1000, -1000] {
            assert_eq!(Lit::from_dimacs(d).to_dimacs(), d);
        }
        assert_eq!(!Lit::from_dimacs(3), Lit::from_dimacs(-3));
        assert_eq!(Lit::from_dimacs(-3).var(), 2);
    }
}
