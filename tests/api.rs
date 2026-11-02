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

/// Adds `out = left & right` (DIMACS literals), with `extra` in every clause.
fn and_gate(s: &mut Solver, gate: (i32, i32, i32), extra: Option<i32>) {
    let (out, left, right) = gate;
    for mut clause in [
        vec![-out, left],
        vec![-out, right],
        vec![out, -left, -right],
    ] {
        clause.extend(extra);
        s.add_clause(&clause);
    }
}

/// Whether `lit` holds when the inputs `1..=inputs` take the bits of `bits`
/// and every gate holds.
fn holds(gates: &[(i32, i32, i32)], inputs: i32, bits: u32, lit: i32) -> bool {
    let mut values = vec![false; gates.last().map_or(inputs, |g| g.0) as usize + 1];
    for v in 1..=inputs {
        values[v as usize] = bits >> (v - 1) & 1 == 1;
    }
    let value = |values: &[bool], l: i32| values[l.unsigned_abs() as usize] == (l > 0);
    for &(out, left, right) in gates {
        values[out as usize] = value(&values, left) && value(&values, right);
    }
    value(&values, lit)
}

/// Clause groups guarded by an activation literal and retired by its
/// negation as a unit (the usual way to retract clauses) do not accumulate
/// over many short calls, which never reach the conflicts that schedule
/// inprocessing, and every answer is that of the remaining formula.
#[test]
fn retired_clause_groups_are_collected() {
    const INPUTS: i32 = 10;
    const ROUNDS: usize = 300;
    const GROUP: usize = 8;
    let mut state = 0x2545_f491_4f6c_dd1du64;
    let mut operand = |vars: i32| {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        let v = ((state >> 1) % vars as u64) as i32 + 1;
        if state & 1 == 0 { v } else { -v }
    };
    let mut s = Solver::new(Options::default());
    let mut gates: Vec<(i32, i32, i32)> = Vec::new();
    let mut vars = INPUTS;
    for _ in 0..40 {
        let gate = (vars + 1, operand(vars), operand(vars));
        vars += 1;
        and_gate(&mut s, gate, None);
        gates.push(gate);
    }
    let persistent = gates.len();
    let (mut sat, mut unsat, mut most) = (0, 0, 0);
    for _ in 0..ROUNDS {
        vars += 1;
        let guard = vars;
        for _ in 0..GROUP {
            let gate = (vars + 1, operand(vars - 1), operand(vars - 1));
            vars += 1;
            and_gate(&mut s, gate, Some(-guard));
            gates.push(gate);
        }
        s.assume(guard);
        s.assume(vars);
        let expected = (0..1u32 << INPUTS).any(|bits| holds(&gates, INPUTS, bits, vars));
        match s.solve() {
            SolveResult::Sat => {
                let bits = (1..=INPUTS)
                    .filter(|&v| s.val(v) == v)
                    .fold(0, |bits, v| bits | 1 << (v - 1));
                assert!(holds(&gates, INPUTS, bits, vars));
                sat += 1;
            }
            SolveResult::Unsat => {
                assert!(!expected);
                unsat += 1;
            }
            SolveResult::Unknown => unreachable!(),
        }
        s.add_clause(&[-guard]);
        for &(out, _, _) in &gates[persistent..] {
            s.add_clause(&[-out]);
        }
        gates.truncate(persistent);
        most = most.max(s.stats().clauses_irredundant);
    }
    assert!(
        sat > 0 && unsat > 0,
        "{sat} satisfiable, {unsat} unsatisfiable"
    );
    // Each round retires 3 * GROUP large clauses, 7200 in all.
    assert!(most < 200, "{most} irredundant large clauses");
    assert!(s.stats().compacts > 0);
}
