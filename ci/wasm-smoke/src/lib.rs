//! Smoke test of crabsat on `wasm32-unknown-unknown` (run by `run.mjs` with
//! Node.js, without any host imports): `smoke()` returns 0 on success and
//! the number of the failed check otherwise; panics trap.

use crabsat::{Options, SolveResult, Solver};

fn pigeon_hole(s: &mut Solver, holes: i32) {
    let var = |p: i32, h: i32| p * holes + h + 1;
    for p in 0..=holes {
        let c: Vec<i32> = (0..holes).map(|h| var(p, h)).collect();
        s.add_clause(&c);
    }
    for h in 0..holes {
        for p in 0..=holes {
            for q in p + 1..=holes {
                s.add_clause(&[-var(p, h), -var(q, h)]);
            }
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn smoke() -> i32 {
    // Unsatisfiable, with inprocessing.
    let mut s = Solver::new(Options::default());
    pigeon_hole(&mut s, 7);
    if s.solve() != SolveResult::Unsat {
        return 1;
    }
    // Incremental use with assumptions and reactivation.
    let mut s = Solver::new(Options::default());
    for i in 1..40 {
        s.add_clause(&[-i, i + 1]);
    }
    if s.solve() != SolveResult::Sat {
        return 2;
    }
    s.assume(1);
    s.assume(-40);
    if s.solve() != SolveResult::Unsat || !s.failed(1) || !s.failed(-40) {
        return 3;
    }
    s.add_clause(&[-20]);
    s.add_clause(&[1, 25]);
    if s.solve() != SolveResult::Sat || s.val(1) != -1 || s.val(25) != 25 {
        return 4;
    }
    // Random 3-SAT near the threshold, model checked.
    let mut x: u64 = 0x2545_f491_4f6c_dd1d;
    let mut clauses = Vec::new();
    let mut s = Solver::new(Options::default());
    for _ in 0..400 {
        let c: Vec<i32> = (0..3)
            .map(|_| {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                let v = (x % 100) as i32 + 1;
                if x & 1 << 20 == 0 { v } else { -v }
            })
            .collect();
        s.add_clause(&c);
        clauses.push(c);
    }
    match s.solve() {
        SolveResult::Sat => {
            if !clauses.iter().all(|c| c.iter().any(|&l| s.val(l) == l)) {
                return 5;
            }
        }
        SolveResult::Unsat => {}
        SolveResult::Unknown => return 6,
    }
    if crabsat::VERSION.is_empty() {
        return 7;
    }
    0
}
