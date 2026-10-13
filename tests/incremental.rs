//! Randomized tests of the incremental interface: sequences of clause
//! additions, assumptions and solve calls are checked against fresh
//! non-incremental solvers.

use crabsat::ipasir::*;
use crabsat::{Options, SolveResult, Solver};
use std::ffi::{CStr, c_int, c_void};

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    fn lit(&mut self, vars: usize) -> i32 {
        let v = self.below(vars as u64) as i32 + 1;
        if self.next() & 1 == 0 { v } else { -v }
    }
}

fn fresh(clauses: &[Vec<i32>], units: &[i32]) -> SolveResult {
    let mut s = Solver::new(Options {
        quiet: true,
        ..Options::default()
    });
    for c in clauses {
        s.add_clause(c);
    }
    for &u in units {
        s.add_clause(&[u]);
    }
    s.solve()
}

/// Number of random runs (`CRABSAT_INCREMENTAL_RUNS` for longer stress tests).
fn runs() -> u64 {
    std::env::var("CRABSAT_INCREMENTAL_RUNS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(150)
}

fn aggressive() -> Options {
    Options {
        incremental: true,
        quiet: true,
        eliminateinit: 1,
        eliminateint: 10,
        probeinit: 1,
        probeint: 10,
        reduceinit: 10,
        reduceint: 10,
        compactlim: 0,
        mineffort: 1000,
        ..Options::default()
    }
}

/// One random incremental run; returns the number of SAT and UNSAT calls
/// and of reactivated variables.
fn run(seed: u64, opts: Options, large: bool) -> (usize, usize, u64) {
    let mut rng = Rng(seed.wrapping_mul(0x9e3779b97f4a7c15) | 1);
    let mut vars = if large {
        150 + rng.below(100) as usize
    } else {
        10 + rng.below(30) as usize
    };
    let mut s = Solver::new(opts);
    let mut clauses: Vec<Vec<i32>> = Vec::new();
    let (mut sat, mut unsat) = (0, 0);
    for round in 0..12 {
        // Grow the formula (sometimes with new variables).
        if rng.below(3) == 0 {
            vars += rng.below(10) as usize;
        }
        let added = if large {
            vars / 2 + rng.below(vars as u64 / 2) as usize + if round == 0 { 3 * vars } else { 0 }
        } else {
            2 * vars + rng.below(2 * vars as u64) as usize
        };
        for _ in 0..added {
            let len = if large { 3 } else { 2 + rng.below(3) as usize };
            let c: Vec<i32> = (0..len).map(|_| rng.lit(vars)).collect();
            s.add_clause(&c);
            clauses.push(c);
        }
        let assumptions: Vec<i32> = (0..rng.below(6)).map(|_| rng.lit(vars)).collect();
        for &a in &assumptions {
            s.assume(a);
        }
        let res = s.solve();
        let expected = fresh(&clauses, &assumptions);
        assert_eq!(res, expected, "seed {seed} round {round}");
        match res {
            SolveResult::Sat => {
                sat += 1;
                for c in &clauses {
                    assert!(
                        c.iter().any(|&l| s.val(l) == l),
                        "seed {seed} round {round}: clause {c:?} falsified"
                    );
                }
                for &a in &assumptions {
                    assert_eq!(s.val(a), a, "seed {seed} round {round}: assumption {a}");
                }
            }
            SolveResult::Unsat => {
                unsat += 1;
                let failed: Vec<i32> = assumptions
                    .iter()
                    .copied()
                    .filter(|&a| s.failed(a))
                    .collect();
                assert_eq!(
                    fresh(&clauses, &failed),
                    SolveResult::Unsat,
                    "seed {seed} round {round}: failed assumptions {failed:?} are not a core"
                );
                if fresh(&clauses, &[]) == SolveResult::Unsat {
                    // The formula itself is unsatisfiable: stop.
                    break;
                }
            }
            SolveResult::Unknown => unreachable!(),
        }
    }
    (sat, unsat, s.stats().reactivated)
}

#[test]
fn random_incremental_default() {
    let (mut sat, mut unsat) = (0, 0);
    for seed in 0..runs() {
        let opts = Options {
            incremental: true,
            quiet: true,
            ..Options::default()
        };
        let (a, b, _) = run(seed, opts, false);
        sat += a;
        unsat += b;
    }
    assert!(sat > 50 && unsat > 50, "sat {sat} unsat {unsat}");
}

#[test]
fn random_incremental_aggressive() {
    let mut reactivated = 0;
    for seed in 1000..1000 + runs() {
        reactivated += run(seed, aggressive(), false).2;
    }
    assert!(reactivated > 0);
    eprintln!("reactivated {reactivated}");
}

#[test]
fn reactivation_of_eliminated_variables() {
    // x1 = x2 & x3 (gate), eliminated by preprocessing; later clauses and
    // assumptions mention x1 again.
    let mut s = Solver::new(aggressive());
    for c in [[-1, 2, 0], [-1, 3, 0], [1, -2, -3]] {
        let c: Vec<i32> = c.into_iter().filter(|&l| l != 0).collect();
        s.add_clause(&c);
    }
    s.add_clause(&[2, 4]);
    s.add_clause(&[3, -4]);
    assert_eq!(s.solve(), SolveResult::Sat);
    s.assume(1);
    s.assume(-4);
    assert_eq!(s.solve(), SolveResult::Sat);
    assert_eq!(s.val(2), 2);
    assert_eq!(s.val(3), 3);
    s.add_clause(&[-1, 4]);
    s.assume(1);
    s.assume(-4);
    assert_eq!(s.solve(), SolveResult::Unsat);
    assert!(s.failed(1) && s.failed(-4));
    s.assume(1);
    assert_eq!(s.solve(), SolveResult::Sat);
    assert_eq!(s.val(4), 4);
}

extern "C" fn count_learned(state: *mut c_void, clause: *mut i32) {
    let mut len = 0;
    while unsafe { *clause.add(len) } != 0 {
        len += 1;
    }
    assert!(len <= 10);
    unsafe { *state.cast::<usize>() += 1 };
}

extern "C" fn stop(_: *mut c_void) -> c_int {
    1
}

#[test]
fn c_interface() {
    unsafe {
        let name = CStr::from_ptr(ipasir_signature());
        assert!(name.to_str().unwrap().starts_with("crabsat"));
        let s = ipasir_init();
        // Pigeon hole 6 into 5, with selector -7 on the "every pigeon in
        // a hole" clauses.
        let var = |p: i32, h: i32| p * 5 + h + 1;
        let sel = 31;
        for p in 0..6 {
            for h in 0..5 {
                ipasir_add(s, var(p, h));
            }
            ipasir_add(s, -sel);
            ipasir_add(s, 0);
        }
        for h in 0..5 {
            for p in 0..6 {
                for q in p + 1..6 {
                    ipasir_add(s, -var(p, h));
                    ipasir_add(s, -var(q, h));
                    ipasir_add(s, 0);
                }
            }
        }
        ipasir_assume(s, sel);
        assert_eq!(ipasir_solve(s), 20);
        assert_eq!(ipasir_failed(s, sel), 1);
        assert_eq!(ipasir_solve(s), 10);
        assert_eq!(ipasir_val(s, sel), -sel);
        ipasir_release(s);

        // Learned clauses of a random 3-SAT formula.
        let s = ipasir_init();
        let mut rng = Rng(12345);
        for _ in 0..850 {
            for _ in 0..3 {
                ipasir_add(s, rng.lit(200));
            }
            ipasir_add(s, 0);
        }
        ipasir_set_terminate(s, std::ptr::null_mut(), Some(stop));
        assert_eq!(ipasir_solve(s), 0);
        ipasir_set_terminate(s, std::ptr::null_mut(), None);
        let mut learned: usize = 0;
        ipasir_set_learn(s, (&raw mut learned).cast(), 10, Some(count_learned));
        assert_ne!(ipasir_solve(s), 0);
        assert!(learned > 0);
        ipasir_release(s);
    }
}

#[test]
fn random_incremental_large() {
    let mut reactivated = 0;
    for seed in 2000..2000 + runs() / 10 {
        let opts = if seed % 2 == 0 {
            aggressive()
        } else {
            Options {
                incremental: true,
                quiet: true,
                ..Options::default()
            }
        };
        reactivated += run(seed, opts, true).2;
    }
    eprintln!("large: reactivated {reactivated}");
}
