//! Tests of the library API used by incremental applications (and by
//! wrappers such as RustSAT backends).

use crabsat::{Callbacks, Options, SolveResult, Solver};

/// Pigeon hole principle `holes + 1` into `holes` (hard enough to need
/// conflicts).
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

#[test]
fn solver_is_send() {
    fn send<T: Send>() {}
    send::<Solver>();
    send::<crabsat::Interrupter>();
}

#[test]
fn defaults_are_incremental() {
    let mut s = Solver::new(Options::default());
    for i in 1..30 {
        s.add_clause(&[-i, i + 1]);
    }
    assert_eq!(s.solve(), SolveResult::Sat);
    // Variables in the middle were most likely eliminated; using them again
    // reactivates them.
    s.add_clause(&[-15]);
    s.add_clause(&[1]);
    assert_eq!(s.solve(), SolveResult::Unsat);
}

struct Borrowing<'a> {
    learned: &'a mut Vec<Vec<i32>>,
    polls: &'a mut usize,
}

impl Callbacks for Borrowing<'_> {
    fn terminate(&mut self) -> bool {
        *self.polls += 1;
        false
    }
    fn learn_limit(&self) -> usize {
        4
    }
    fn learn(&mut self, clause: &[i32]) {
        self.learned.push(clause.to_vec());
    }
}

#[test]
fn callbacks_may_borrow() {
    let mut learned = Vec::new();
    let mut polls = 0;
    let mut s = Solver::new(Options::default());
    pigeon_hole(&mut s, 6);
    let res = s.solve_with(&mut Borrowing {
        learned: &mut learned,
        polls: &mut polls,
    });
    assert_eq!(res, SolveResult::Unsat);
    assert!(polls > 0);
    assert!(!learned.is_empty());
    assert!(learned.iter().all(|c| c.len() <= 4 && !c.contains(&0)));
}

struct Stop;
impl Callbacks for Stop {
    fn terminate(&mut self) -> bool {
        true
    }
}

#[test]
fn terminate_before_search() {
    let mut s = Solver::new(Options::default());
    s.add_clause(&[1, -2]);
    s.add_clause(&[2, -3]);
    assert_eq!(s.solve_with(&mut Stop), SolveResult::Unknown);
    assert_eq!(s.solve(), SolveResult::Sat);
}

#[test]
fn interrupter_stops_one_call() {
    let mut s = Solver::new(Options::default());
    pigeon_hole(&mut s, 9);
    let i = s.interrupter();
    let t = std::thread::spawn(move || {
        std::thread::sleep(std::time::Duration::from_millis(50));
        i.interrupt();
    });
    assert_eq!(s.solve(), SolveResult::Unknown);
    t.join().unwrap();
    // The interrupt does not carry over.
    let mut small = Solver::new(Options::default());
    let i = small.interrupter();
    i.interrupt();
    small.add_clause(&[1]);
    assert_eq!(small.solve(), SolveResult::Unknown);
    assert_eq!(small.solve(), SolveResult::Sat);
}

#[test]
fn limits_are_per_call() {
    let mut s = Solver::new(Options::default());
    pigeon_hole(&mut s, 8);
    s.set_conflict_limit(Some(200));
    assert_eq!(s.solve(), SolveResult::Unknown);
    let after_first = s.stats().conflicts;
    assert_eq!(s.solve(), SolveResult::Unknown);
    assert!(
        s.stats().conflicts > after_first + 100,
        "second call got a new budget"
    );
    s.set_conflict_limit(None);
    assert_eq!(s.solve(), SolveResult::Unsat);
}

/// Every call stops at or before its conflict limit, and exactly at it when
/// the limit stops the call, also over chains of conflicts and on-the-fly
/// strengthening.  Calls with small limits under changing assumptions
/// resume the same search and agree with an unlimited solver.
#[test]
fn conflict_limit_is_exact() {
    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    for instance in 0..40 {
        let vars = 60;
        let clauses: Vec<Vec<i32>> = (0..255)
            .map(|_| {
                (0..3)
                    .map(|_| {
                        let v = (next() % vars) as i32 + 1;
                        if next() & 1 == 0 { v } else { -v }
                    })
                    .collect()
            })
            .collect();
        let mut limited = Solver::new(Options::default());
        if instance % 2 == 0 {
            pigeon_hole(&mut limited, 5);
        }
        for c in &clauses {
            limited.add_clause(c);
        }
        let mut reference = Solver::new(Options::default());
        if instance % 2 == 0 {
            pigeon_hole(&mut reference, 5);
        }
        for c in &clauses {
            reference.add_clause(c);
        }
        for query in 0..20 {
            let assumptions: Vec<i32> = (0..query % 4)
                .map(|_| {
                    let v = (next() % vars) as i32 + 1;
                    if next() & 1 == 0 { v } else { -v }
                })
                .collect();
            // A limit of zero makes no progress, so it is checked alone.
            for &a in &assumptions {
                limited.assume(a);
            }
            limited.set_conflict_limit(Some(0));
            let before = limited.stats().conflicts;
            let answer = limited.solve();
            let spent = limited.stats().conflicts - before;
            assert!(
                spent == 0 || (spent == 1 && answer == SolveResult::Unsat),
                "instance {instance} query {query}"
            );
            let limit = 1 + next() % 8;
            let answer = loop {
                for &a in &assumptions {
                    limited.assume(a);
                }
                limited.set_conflict_limit(Some(limit));
                let before = limited.stats().conflicts;
                let answer = limited.solve();
                let spent = limited.stats().conflicts - before;
                match answer {
                    SolveResult::Unknown => {
                        assert_eq!(spent, limit, "instance {instance} query {query}")
                    }
                    _ => {
                        assert!(spent <= limit, "instance {instance} query {query}");
                        break answer;
                    }
                }
            };
            for &a in &assumptions {
                reference.assume(a);
            }
            assert_eq!(
                answer,
                reference.solve(),
                "instance {instance} query {query}"
            );
        }
    }
}

#[test]
fn forced_phases() {
    let mut s = Solver::new(Options {
        lucky: false,
        ..Options::default()
    });
    s.add_clause(&[1, 2, 3]);
    s.add_clause(&[-4, 5]);
    for d in [-1, -2, 3, 4, 5] {
        s.phase(d);
    }
    assert_eq!(s.solve(), SolveResult::Sat);
    for d in [-1, -2, 3, 4, 5] {
        assert_eq!(s.val(d), d);
    }
    s.unphase(4);
    s.phase(-5);
    assert_eq!(s.solve(), SolveResult::Sat);
    assert_eq!(s.val(-5), -5);
    assert_eq!(s.val(-4), -4);
}

#[test]
fn freezing() {
    let mut s = Solver::new(Options::default());
    s.add_clause(&[1, -2]);
    s.freeze(1);
    s.freeze(1);
    assert!(s.is_frozen(1) && !s.is_frozen(2));
    s.melt(1);
    assert!(s.is_frozen(1));
    s.melt(1);
    assert!(!s.is_frozen(1));
    s.melt(1);
    assert!(!s.is_frozen(1));
    // Frozen variables are not eliminated.
    let mut s = Solver::new(Options::default());
    for i in 1..30 {
        s.add_clause(&[-i, i + 1]);
    }
    s.freeze(15);
    assert_eq!(s.solve(), SolveResult::Sat);
    assert_eq!(s.stats().reactivated, 0);
    s.add_clause(&[15]);
    assert_eq!(s.solve(), SolveResult::Sat);
    assert_eq!(s.stats().reactivated, 0);
    assert_eq!(s.val(29), 29);
}

#[test]
fn failed_assumptions_form_a_core() {
    let mut s = Solver::new(Options::default());
    s.add_clause(&[-1, -2]);
    s.add_clause(&[3, 4]);
    for a in [1, 2, 5] {
        s.assume(a);
    }
    assert_eq!(s.solve(), SolveResult::Unsat);
    let mut core: Vec<i32> = s.failed_assumptions().collect();
    core.sort();
    assert_eq!(core, vec![1, 2]);
    // Assumptions are cleared after each call.
    assert_eq!(s.solve(), SolveResult::Sat);
    assert_eq!(s.failed_assumptions().count(), 0);
}

#[test]
#[should_panic(expected = "invalid literal")]
fn zero_literal_is_rejected() {
    let mut s = Solver::new(Options::default());
    s.assume(0);
}
