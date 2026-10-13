//! Congruence closure on extracted gates (in the spirit of Kissat
//! `congruence.c`).
//!
//! AND, ITE and XOR gates are extracted from the irredundant clauses.  Two
//! gates of the same kind with equivalent inputs have equivalent outputs.
//! Found equivalences are added as binary clauses (with RUP proofs, using
//! case splits over the inputs for ITE and XOR gates) and then removed by
//! equivalent literal substitution.

use crate::arena::CRef;
use crate::solver::{Solver, ELIMINATED};
use crate::types::Lit;
use crate::watch::{self, Watch};
use std::collections::HashMap;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum Kind {
    And,
    Ite,
    Xor,
}

/// Result of normalizing a gate.
enum Norm {
    /// Hash key and output literal.
    Key((Kind, Vec<Lit>), Lit),
    /// The output is equivalent to a literal.
    Equiv(Lit, Lit),
    /// The literal is implied.
    Unit(Lit),
}

/// Input variables of one or two gates (for case split proofs).
fn input_vars(g1: &Gate, g2: Option<&Gate>) -> Vec<Lit> {
    let mut v: Vec<Lit> = g1.rhs.iter().map(|l| Lit::new(l.var(), false)).collect();
    if let Some(g2) = g2 {
        v.extend(g2.rhs.iter().map(|l| Lit::new(l.var(), false)));
    }
    v.sort_unstable();
    v.dedup();
    v
}

#[derive(Clone, Debug)]
struct Gate {
    kind: Kind,
    lhs: Lit,
    /// Inputs as extracted (actual literals of the clauses).
    rhs: Vec<Lit>,
    /// Inputs of XOR gates are variables (positive literals) and the
    /// constant parity is folded into `lhs`.
    garbage: bool,
}

struct UnionFind {
    /// `parent[v]` is a literal equivalent to the positive literal of `v`.
    parent: Vec<Lit>,
    /// Variables in the class of a representative variable.
    members: Vec<Vec<u32>>,
}

impl UnionFind {
    fn new(vars: usize) -> Self {
        UnionFind {
            parent: (0..vars as u32).map(|v| Lit::new(v, false)).collect(),
            members: (0..vars as u32).map(|v| vec![v]).collect(),
        }
    }

    fn find(&mut self, lit: Lit) -> Lit {
        let p = self.parent[lit.vidx()];
        if p.var() == lit.var() {
            return lit;
        }
        let r = self.find(p);
        self.parent[lit.vidx()] = r;
        if lit.negated() { !r } else { r }
    }

    /// Merge the classes of `a` and `b` (`a = b`).  Returns the variables
    /// whose representative changed.
    fn union(&mut self, a: Lit, b: Lit) -> Vec<u32> {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra == rb {
            return Vec::new();
        }
        debug_assert!(ra != !rb);
        let (small, large) = if ra.var() < rb.var() { (ra, rb) } else { (rb, ra) };
        self.parent[large.vidx()] = if large.negated() { !small } else { small };
        let moved = std::mem::take(&mut self.members[large.vidx()]);
        self.members[small.vidx()].extend_from_slice(&moved);
        moved
    }
}

impl Solver {
    pub fn congruence(&mut self) -> bool {
        let start = std::time::Instant::now();
        let res = self.congruence_untimed();
        self.stats.time_congruence += start.elapsed().as_secs_f64();
        res
    }

    /// Run congruence closure.  Returns false on inconsistency.
    fn congruence_untimed(&mut self) -> bool {
        debug_assert_eq!(self.level, 0);
        if !self.opts.congruence || self.delay_congruence.delaying() {
            return true;
        }
        self.stats.congruences += 1;
        let gates = self.extract_gates();
        if self.verbose(2) {
            let count = |k: Kind| gates.iter().filter(|g| g.kind == k).count();
            println!(
                "c [congruence-{}] extracted {} AND {} ITE {} XOR gates",
                self.stats.congruences,
                count(Kind::And),
                count(Kind::Ite),
                count(Kind::Xor)
            );
        }
        if gates.is_empty() {
            self.delay_congruence.bump();
            return true;
        }
        let equivalences = self.close_congruences(gates);
        let active = (self.vars as u32 - self.eliminated).max(1);
        if (equivalences as f64) / (active as f64) < 0.001 {
            self.delay_congruence.bump();
        } else {
            self.delay_congruence.reduce();
        }
        if self.verbose(2) {
            println!("c [congruence-{}] found {} equivalences", self.stats.congruences, equivalences);
        }
        if self.inconsistent {
            return false;
        }
        if equivalences == 0 {
            return true;
        }
        self.stats.congruent += equivalences as u64;
        self.substitute()
    }

    // ------------------------------------------------------------------
    // Gate extraction.

    fn extract_gates(&mut self) -> Vec<Gate> {
        let n = 2 * self.vars;
        // Occurrences of irredundant large clauses of size <= 5 (for ITE and
        // XOR) and all sizes (for AND base clauses).
        let mut occs: Vec<Vec<CRef>> = vec![Vec::new(); n];
        let mut c = 0;
        while (c as usize) < self.arena.len() {
            let next = self.arena.next(c);
            if !self.arena.garbage(c) && !self.arena.redundant(c) {
                if self.arena.lits(c).iter().all(|&l| self.value(l) == 0) {
                    for &l in self.arena.lits(c) {
                        occs[l.idx()].push(c);
                    }
                }
            }
            c = next;
        }
        let mut gates = Vec::new();
        if self.opts.congruenceands {
            self.extract_and_gates(&occs, &mut gates);
        }
        if self.opts.congruenceites {
            self.extract_ite_gates(&occs, &mut gates);
        }
        if self.opts.congruencexors {
            self.extract_xor_gates(&occs, &mut gates);
        }
        gates
    }

    fn active_lit(&self, l: Lit) -> bool {
        self.value(l) == 0 && self.flags[l.vidx()] & ELIMINATED == 0
    }

    /// `lhs = AND(rhs)`: binary clauses `(!lhs | r)` and base clause
    /// `(lhs | !r1 | ... | !rn)`.
    fn extract_and_gates(&mut self, occs: &[Vec<CRef>], gates: &mut Vec<Gate>) {
        let arity_limit = self.opts.congruenceandarity as usize;
        for idx in 0..2 * self.vars {
            let lhs = Lit(idx as u32);
            if !self.active_lit(lhs) || occs[lhs.idx()].is_empty() {
                continue;
            }
            let mut marked = Vec::new();
            for w in watch::iter(&self.watches[(!lhs).idx()]) {
                if let Watch::Binary(other) = w {
                    if self.value(other) == 0 && self.marks[other.idx()] == 0 {
                        self.marks[other.idx()] = 1;
                        marked.push(other);
                    }
                }
            }
            if marked.len() >= 2 {
                for &c in &occs[lhs.idx()] {
                    let lits = self.arena.lits(c);
                    if lits.len() - 1 > arity_limit || lits.len() - 1 > marked.len() {
                        continue;
                    }
                    if lits.iter().all(|&l| l == lhs || self.marks[(!l).idx()] != 0) {
                        let mut rhs: Vec<Lit> =
                            lits.iter().filter(|&&l| l != lhs).map(|&l| !l).collect();
                        rhs.sort_unstable();
                        gates.push(Gate { kind: Kind::And, lhs, rhs, garbage: false });
                    }
                }
            }
            for l in marked {
                self.marks[l.idx()] = 0;
            }
        }
    }

    /// `lhs = c ? t : e` from the four ternary clauses
    /// `(!c | !t | lhs) (!c | t | !lhs) (c | !e | lhs) (c | e | !lhs)`.
    fn extract_ite_gates(&mut self, occs: &[Vec<CRef>], gates: &mut Vec<Gate>) {
        // Hash set of ternary clauses.
        let mut ternary: std::collections::HashSet<[Lit; 3]> = std::collections::HashSet::new();
        let key = |mut a: [Lit; 3]| {
            a.sort_unstable();
            a
        };
        let mut c = 0;
        while (c as usize) < self.arena.len() {
            let next = self.arena.next(c);
            if !self.arena.garbage(c) && !self.arena.redundant(c) && self.arena.size(c) == 3 {
                let l = self.arena.lits(c);
                ternary.insert(key([l[0], l[1], l[2]]));
            }
            c = next;
        }
        let has = |a: Lit, b: Lit, c: Lit| ternary.contains(&key([a, b, c]));
        let mut seen: std::collections::HashSet<(Lit, Lit, Lit, Lit)> = Default::default();
        for idx in 0..2 * self.vars {
            let lhs = Lit(idx as u32);
            if !self.active_lit(lhs) {
                continue;
            }
            // Clauses (!c | !t | lhs).
            for &cl in &occs[lhs.idx()] {
                let lits = self.arena.lits(cl);
                if lits.len() != 3 {
                    continue;
                }
                let others: Vec<Lit> = lits.iter().copied().filter(|&l| l != lhs).collect();
                for (nc, nt) in [(others[0], others[1]), (others[1], others[0])] {
                    let (cond, then) = (!nc, !nt);
                    if cond.var() == then.var() || !has(!cond, then, !lhs) {
                        continue;
                    }
                    if then.var() == lhs.var() {
                        continue;
                    }
                    // Find e with (c | !e | lhs) and (c | e | !lhs).
                    for &d in &occs[cond.idx()] {
                        let dl = self.arena.lits(d);
                        if dl.len() != 3 || !dl.contains(&lhs) {
                            continue;
                        }
                        let ne = dl.iter().copied().find(|&l| l != cond && l != lhs).unwrap();
                        let e = !ne;
                        if e.var() == cond.var() || e.var() == lhs.var() || e.var() == then.var() {
                            continue;
                        }
                        if !has(cond, e, !lhs) {
                            continue;
                        }
                        if seen.insert((lhs, cond, then, e)) {
                            gates.push(Gate {
                                kind: Kind::Ite,
                                lhs,
                                rhs: vec![cond, then, e],
                                garbage: false,
                            });
                        }
                    }
                }
            }
        }
    }

    /// XOR constraints over 3..=arity+1 variables given by all clauses with
    /// the same parity of negations.  Every variable can be the output.
    fn extract_xor_gates(&mut self, _occs: &[Vec<CRef>], gates: &mut Vec<Gate>) {
        let max_size = self.opts.congruencexorarity as usize + 1;
        // Group clauses by variable set.
        let mut groups: HashMap<Vec<u32>, Vec<u32>> = HashMap::new();
        let mut c = 0;
        while (c as usize) < self.arena.len() {
            let next = self.arena.next(c);
            if !self.arena.garbage(c) && !self.arena.redundant(c) {
                let lits = self.arena.lits(c);
                if lits.len() <= max_size && lits.iter().all(|&l| self.value(l) == 0) {
                    let mut vars: Vec<u32> = lits.iter().map(|l| l.var()).collect();
                    vars.sort_unstable();
                    // Sign pattern as bit mask in sorted variable order.
                    let mut sorted = lits.to_vec();
                    sorted.sort_unstable_by_key(|l| l.var());
                    let mask = sorted
                        .iter()
                        .enumerate()
                        .fold(0u32, |m, (i, l)| m | ((l.negated() as u32) << i));
                    groups.entry(vars).or_default().push(mask);
                }
            }
            c = next;
        }
        for (vars, masks) in groups {
            let k = vars.len();
            if k < 3 {
                continue;
            }
            if vars.windows(2).any(|w| w[0] == w[1]) {
                continue;
            }
            let needed = 1usize << (k - 1);
            if masks.len() < needed {
                continue;
            }
            for parity in 0..2u32 {
                let mut present = vec![false; 1 << k];
                for &m in &masks {
                    if m.count_ones() % 2 == parity {
                        present[m as usize] = true;
                    }
                }
                let complete = (0..1u32 << k)
                    .filter(|m| m.count_ones() % 2 == parity)
                    .all(|m| present[m as usize]);
                if !complete {
                    continue;
                }
                // A clause excludes the assignment falsifying it, which sets
                // `xi = negated(i)`, so excluded assignments have as many
                // true variables as negated literals.  Hence all allowed
                // assignments satisfy `x1 ^ ... ^ xk = 1 - parity`.
                let rhs_parity = 1 - parity;
                for out in 0..k {
                    let inputs: Vec<Lit> = (0..k)
                        .filter(|&i| i != out)
                        .map(|i| Lit::new(vars[i], false))
                        .collect();
                    // x_out = XOR(inputs) ^ rhs_parity.
                    let lhs = Lit::new(vars[out], rhs_parity == 1);
                    if !self.active_lit(lhs) {
                        continue;
                    }
                    gates.push(Gate { kind: Kind::Xor, lhs, rhs: inputs, garbage: false });
                }
            }
        }
    }

    // ------------------------------------------------------------------
    // Closure.

    fn normalize_and(mut rhs: Vec<Lit>, lhs: Lit) -> Norm {
        rhs.sort_unstable();
        rhs.dedup();
        if rhs.windows(2).any(|w| w[0] == !w[1]) {
            return Norm::Unit(!lhs);
        }
        if rhs.len() == 1 {
            return Norm::Equiv(lhs, rhs[0]);
        }
        Norm::Key((Kind::And, rhs), lhs)
    }

    /// `lhs = XOR(lits)`: signs are folded into the output.
    fn normalize_xor(lits: &[Lit], mut lhs: Lit) -> Norm {
        let mut vars: Vec<Lit> = Vec::new();
        for &r in lits {
            if r.negated() {
                lhs = !lhs;
            }
            vars.push(Lit::new(r.var(), false));
        }
        vars.sort_unstable();
        // x ^ x = 0: remove pairs.
        let mut reduced: Vec<Lit> = Vec::new();
        for v in vars {
            if reduced.last() == Some(&v) {
                reduced.pop();
            } else {
                reduced.push(v);
            }
        }
        match reduced.len() {
            0 => Norm::Unit(!lhs),
            1 => Norm::Equiv(lhs, reduced[0]),
            _ => Norm::Key((Kind::Xor, reduced), lhs),
        }
    }

    /// Normalize gate inputs under the current equivalences.
    fn normalize_gate(uf: &mut UnionFind, g: &Gate) -> Norm {
        let lhs = g.lhs;
        match g.kind {
            Kind::And => Self::normalize_and(g.rhs.iter().map(|&l| uf.find(l)).collect(), lhs),
            Kind::Xor => {
                let lits: Vec<Lit> = g.rhs.iter().map(|&l| uf.find(l)).collect();
                Self::normalize_xor(&lits, lhs)
            }
            Kind::Ite => {
                let (mut c, mut t, mut e) =
                    (uf.find(g.rhs[0]), uf.find(g.rhs[1]), uf.find(g.rhs[2]));
                let mut lhs = lhs;
                if c.negated() {
                    c = !c;
                    std::mem::swap(&mut t, &mut e);
                }
                if t == e {
                    return Norm::Equiv(lhs, t);
                }
                if t == !e {
                    // c ? t : !t = !(c ^ t)
                    return Self::normalize_xor(&[c, t], !lhs);
                }
                if t == c {
                    // c | e = !(!c & !e)
                    return Self::normalize_and(vec![!c, !e], !lhs);
                }
                if t == !c {
                    return Self::normalize_and(vec![!c, e], lhs);
                }
                if e == c {
                    return Self::normalize_and(vec![c, t], lhs);
                }
                if e == !c {
                    // !c | t = !(c & !t)
                    return Self::normalize_and(vec![c, !t], !lhs);
                }
                if t.negated() {
                    t = !t;
                    e = !e;
                    lhs = !lhs;
                }
                Norm::Key((Kind::Ite, vec![c, t, e]), lhs)
            }
        }
    }

    fn close_congruences(&mut self, mut gates: Vec<Gate>) -> usize {
        let mut uf = UnionFind::new(self.vars);
        let mut table: HashMap<(Kind, Vec<Lit>), usize> = HashMap::new();
        let mut gates_of_var: Vec<Vec<usize>> = vec![Vec::new(); self.vars];
        for (i, g) in gates.iter().enumerate() {
            for &l in &g.rhs {
                gates_of_var[l.vidx()].push(i);
            }
        }
        let mut queue: Vec<usize> = (0..gates.len()).rev().collect();
        let mut keys: Vec<Option<(Kind, Vec<Lit>)>> = vec![None; gates.len()];
        let mut found = 0;
        while let Some(i) = queue.pop() {
            if gates[i].garbage || self.inconsistent {
                continue;
            }
            if let Some(old) = keys[i].take() {
                if table.get(&old) == Some(&i) {
                    table.remove(&old);
                }
            }
            // Equivalence (or unit) implied by gate `i`, possibly together
            // with a congruent gate `j`.
            let (lhs, other, j) = match Self::normalize_gate(&mut uf, &gates[i]) {
                Norm::Unit(unit) => {
                    gates[i].garbage = true;
                    if self.value(unit) == 0 {
                        let inputs = input_vars(&gates[i], None);
                        if inputs.len() <= 8 {
                            self.prove_by_cases(&[unit], &inputs);
                            self.assign_unit(unit);
                        }
                    } else if self.value(unit) < 0 {
                        let inputs = input_vars(&gates[i], None);
                        if inputs.len() <= 8 {
                            self.prove_by_cases(&[unit], &inputs);
                            self.mark_inconsistent();
                        }
                    }
                    continue;
                }
                Norm::Equiv(lhs, other) => {
                    gates[i].garbage = true;
                    (lhs, other, None)
                }
                Norm::Key(key, lhs) => match table.get(&key) {
                    Some(&j) if j != i && !gates[j].garbage => {
                        gates[i].garbage = true;
                        match Self::normalize_gate(&mut uf, &gates[j]) {
                            Norm::Key(_, other_lhs) => (lhs, other_lhs, Some(j)),
                            _ => continue,
                        }
                    }
                    _ => {
                        table.insert(key.clone(), i);
                        keys[i] = Some(key);
                        continue;
                    }
                },
            };
            let (a, b) = (uf.find(lhs), uf.find(other));
            if self.opts.verbose >= 4 {
                println!("c congruence gate {:?} lhs {} other {} via {:?} (reps {} {})",
                    gates[i], lhs, other, j.map(|j| &gates[j]), a, b);
            }
            if a == b {
                continue;
            }
            let inputs = input_vars(&gates[i], j.map(|j| &gates[j]));
            let direct = gates[i].kind == Kind::And
                && j.is_none_or(|j| gates[j].kind == Kind::And);
            if !direct && inputs.len() > 8 {
                continue;
            }
            if a == !b {
                // Equivalent to its own negation: unsatisfiable.
                self.add_equivalence_lemmas(lhs, other, &inputs, direct);
                if let Some(p) = self.proof.as_mut() {
                    p.add(&[!lhs]);
                    p.add(&[lhs]);
                }
                self.mark_inconsistent();
                return found;
            }
            if self.value(lhs) != 0 || self.value(other) != 0 {
                continue;
            }
            self.add_equivalence_lemmas(lhs, other, &inputs, direct);
            found += 1;
            // Gates using variables whose representative changed must be
            // rehashed.
            for v in uf.union(lhs, other) {
                queue.extend(gates_of_var[v as usize].iter().copied());
            }
        }
        found
    }

    /// Add `target` with a RUP proof by case splitting over `inputs`.
    fn prove_by_cases(&mut self, target: &[Lit], inputs: &[Lit]) {
        let Some(p) = self.proof.as_mut() else { return };
        // Variables of the target are assigned anyway.
        let inputs: Vec<Lit> =
            inputs.iter().copied().filter(|v| target.iter().all(|t| t.var() != v.var())).collect();
        let cube = |level: usize, m: u32| {
            let mut lits = target.to_vec();
            for (i, &v) in inputs[..level].iter().enumerate() {
                lits.push(if m & (1 << i) != 0 { !v } else { v });
            }
            lits
        };
        for level in (1..=inputs.len()).rev() {
            for m in 0..(1u32 << level) {
                p.add(&cube(level, m));
            }
        }
        p.add(target);
        for level in 1..=inputs.len() {
            for m in 0..(1u32 << level) {
                p.delete(&cube(level, m));
            }
        }
    }

    /// Add `a = b` as two binary clauses.  AND gates have direct RUP proofs,
    /// otherwise a case split over the inputs is used.
    fn add_equivalence_lemmas(&mut self, a: Lit, b: Lit, inputs: &[Lit], direct: bool) {
        if !direct {
            self.prove_by_cases(&[!a, b], inputs);
            self.prove_by_cases(&[a, !b], inputs);
            // `add_equivalence` adds the binaries again (harmless).
        }
        self.add_equivalence(a, b);
    }

    fn add_equivalence(&mut self, a: Lit, b: Lit) {
        if let Some(p) = self.proof.as_mut() {
            p.add(&[!a, b]);
            p.add(&[a, !b]);
        }
        self.new_binary(!a, b);
        self.new_binary(a, !b);
    }
}
