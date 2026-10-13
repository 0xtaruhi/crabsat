use crabsat::{Options, SolveResult, Solver};

fn solve(vars: usize, clauses: &[Vec<i32>], opts: Options) -> (SolveResult, Solver) {
    let mut s = Solver::new(opts);
    s.reserve_vars(vars);
    for c in clauses {
        s.add_clause(c);
    }
    let res = s.solve();
    if res == SolveResult::Sat {
        let model = s.model();
        for c in clauses {
            assert!(
                c.iter().any(|&l| model[l.unsigned_abs() as usize - 1] == l),
                "clause {c:?} not satisfied"
            );
        }
    }
    (res, s)
}

/// Pigeon hole principle: `holes + 1` pigeons into `holes` holes.
fn pigeon_hole(holes: i32) -> (usize, Vec<Vec<i32>>) {
    let pigeons = holes + 1;
    let var = |p: i32, h: i32| p * holes + h + 1;
    let mut clauses = Vec::new();
    for p in 0..pigeons {
        clauses.push((0..holes).map(|h| var(p, h)).collect());
    }
    for h in 0..holes {
        for p in 0..pigeons {
            for q in p + 1..pigeons {
                clauses.push(vec![-var(p, h), -var(q, h)]);
            }
        }
    }
    ((pigeons * holes) as usize, clauses)
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

fn random_3sat(vars: usize, clauses: usize, seed: u64) -> Vec<Vec<i32>> {
    let mut rng = Rng(seed * 2654435761 + 1);
    (0..clauses)
        .map(|_| {
            (0..3)
                .map(|_| {
                    let v = (rng.next() % vars as u64) as i32 + 1;
                    if rng.next() & 1 == 0 { v } else { -v }
                })
                .collect()
        })
        .collect()
}

#[test]
fn trivial() {
    assert_eq!(solve(0, &[], Options::default()).0, SolveResult::Sat);
    assert_eq!(
        solve(1, &[vec![]], Options::default()).0,
        SolveResult::Unsat
    );
    assert_eq!(
        solve(1, &[vec![1], vec![-1]], Options::default()).0,
        SolveResult::Unsat
    );
    assert_eq!(
        solve(
            2,
            &[vec![1, 2], vec![-1, 2], vec![1, -2]],
            Options::default()
        )
        .0,
        SolveResult::Sat
    );
    assert_eq!(
        solve(
            2,
            &[vec![1, 2], vec![-1, 2], vec![1, -2], vec![-1, -2]],
            Options::default()
        )
        .0,
        SolveResult::Unsat
    );
}

#[test]
fn pigeon_holes() {
    for holes in 2..=7 {
        let (vars, clauses) = pigeon_hole(holes);
        assert_eq!(
            solve(vars, &clauses, Options::default()).0,
            SolveResult::Unsat,
            "php {holes}"
        );
    }
}

#[test]
fn random_3sat_all_modes() {
    for stable in 0..=2 {
        let mut sat = 0;
        for seed in 0..60 {
            let clauses = random_3sat(80, 340, seed);
            let opts = Options {
                stable,
                ..Options::default()
            };
            if solve(80, &clauses, opts).0 == SolveResult::Sat {
                sat += 1;
            }
        }
        assert!(
            sat > 5 && sat < 60,
            "unexpected SAT ratio {sat}/60 (stable={stable})"
        );
    }
}

#[test]
fn conflict_limit_gives_unknown() {
    let (vars, clauses) = pigeon_hole(10);
    let mut s = Solver::new(Options::default());
    s.reserve_vars(vars);
    for c in &clauses {
        s.add_clause(c);
    }
    s.set_conflict_limit(Some(100));
    assert_eq!(s.solve(), SolveResult::Unknown);
}
