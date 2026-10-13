//! SAT sweeping (Kissat `sweep.c`): for a variable, the clauses in its
//! neighbourhood (the "environment") are solved with the small `Kitten`
//! solver to find backbone literals and equivalences.  Since the
//! environment is a subset of the formula, everything implied by it is
//! implied by the formula.  Kitten's learned clauses serve as proof.

use crate::arena::CRef;
use crate::kitten::{Kitten, KittenResult};
use crate::solver::{ELIMINATED, SWEPT, Solver};
use crate::types::{Lit, Var};
use crate::watch::{self, Watch};

struct Environment {
    /// Local index -> global variable.
    vars: Vec<Var>,
    clauses: Vec<Vec<Lit>>,
}

impl Solver {
    pub fn sweep(&mut self) -> bool {
        let start = std::time::Instant::now();
        let res = self.sweep_untimed();
        self.stats.time_sweep += start.elapsed().as_secs_f64();
        res
    }

    /// Run SAT sweeping.  Returns false on inconsistency.
    fn sweep_untimed(&mut self) -> bool {
        debug_assert_eq!(self.level, 0);
        if !self.opts.sweep || self.inconsistent {
            return !self.inconsistent;
        }
        if self.delay_sweep.delaying() {
            return true;
        }
        self.stats.sweeps += 1;
        let limit = self.stats.sweep_ticks
            + self.effort_limit_from(self.last_probe_ticks, self.opts.sweepeffort);
        // Occurrences of irredundant large clauses.
        let mut occs: Vec<Vec<CRef>> = vec![Vec::new(); 2 * self.vars];
        let mut c = 0;
        while (c as usize) < self.arena.len() {
            let next = self.arena.next(c);
            if !self.arena.garbage(c) && !self.arena.redundant(c) {
                for &l in self.arena.lits(c) {
                    occs[l.idx()].push(c);
                }
            }
            c = next;
        }
        // Number of clauses containing the variable (independent of where
        // large clauses happen to be watched).
        let occurrences = |s: &Solver, v: usize| {
            let p = Lit::new(v as Var, false);
            let binaries = |l: Lit| {
                watch::iter(&s.watches[l.idx()])
                    .filter(|w| matches!(w, Watch::Binary(_)))
                    .count()
            };
            binaries(p) + binaries(!p) + occs[p.idx()].len() + occs[(!p).idx()].len()
        };
        let mut candidates: Vec<(usize, Var)> = (0..self.vars)
            .filter(|&v| self.sweepable(v) && self.flags[v] & SWEPT == 0)
            .map(|v| (occurrences(self, v), v as Var))
            .filter(|&(o, _)| o > 0)
            .collect();
        if candidates.is_empty() {
            // Everything was swept: start over.
            for f in &mut self.flags {
                *f &= !SWEPT;
            }
            return true;
        }
        candidates.sort_unstable();
        let mut map: Vec<u32> = vec![u32::MAX; self.vars];
        let before_units = self.stats.sweep_units;
        let before_equivalences = self.stats.sweep_equivalences;
        for &(_, v) in &candidates {
            if self.stats.sweep_ticks > limit || self.terminated() || self.inconsistent {
                break;
            }
            if !self.sweepable(v as usize) {
                continue;
            }
            self.flags[v as usize] |= SWEPT;
            let env = self.environment(v, &occs, &mut map);
            let env_lits: usize = env.clauses.iter().map(|c| c.len()).sum();
            self.stats.sweep_ticks += 1 + (env_lits / 8) as u64;
            for &u in &env.vars {
                map[u as usize] = u32::MAX;
            }
            if env.vars.len() < 2 || env.clauses.is_empty() {
                continue;
            }
            self.sweep_environment(&env);
        }
        if self.verbose(2) {
            println!(
                "c [sweep-{}] found {} units and {} equivalences",
                self.stats.sweeps,
                self.stats.sweep_units - before_units,
                self.stats.sweep_equivalences - before_equivalences
            );
        }
        if self.stats.sweep_units == before_units
            && self.stats.sweep_equivalences == before_equivalences
        {
            self.delay_sweep.bump();
        } else {
            self.delay_sweep.reduce();
        }
        if self.inconsistent {
            return false;
        }
        if self.stats.sweep_equivalences > before_equivalences {
            return self.substitute();
        }
        if self.stats.sweep_units > before_units {
            return self.resync_watches();
        }
        true
    }

    fn sweepable(&self, v: usize) -> bool {
        self.flags[v] & ELIMINATED == 0 && self.values[2 * v] == 0
    }

    /// Collect clauses around `root` up to the configured depth and size.
    fn environment(&self, root: Var, occs: &[Vec<CRef>], map: &mut [u32]) -> Environment {
        let max_vars = self.opts.sweepvars as usize;
        let max_clauses = self.opts.sweepclauses as usize;
        let mut env = Environment {
            vars: vec![root],
            clauses: Vec::new(),
        };
        map[root as usize] = 0;
        let mut seen_clauses: crate::fxhash::FxHashSet<CRef> = Default::default();
        let mut seen_binaries: crate::fxhash::FxHashSet<(Lit, Lit)> = Default::default();
        let mut frontier = vec![root];
        'depth: for _ in 0..self.opts.sweepdepth {
            let mut next_frontier = Vec::new();
            for &v in &frontier {
                for sign in [false, true] {
                    let lit = Lit::new(v, sign);
                    let mut new: Vec<Vec<Lit>> = Vec::new();
                    for w in watch::iter(&self.watches[lit.idx()]) {
                        if let Watch::Binary(other) = w {
                            if self.value(other) != 0 {
                                continue;
                            }
                            let key = if lit < other {
                                (lit, other)
                            } else {
                                (other, lit)
                            };
                            if seen_binaries.insert(key) {
                                new.push(vec![lit, other]);
                            }
                        }
                    }
                    for &c in &occs[lit.idx()] {
                        if self.arena.garbage(c) {
                            continue;
                        }
                        let lits = self.arena.lits(c);
                        if lits.iter().any(|&l| self.value(l) > 0) {
                            continue;
                        }
                        if seen_clauses.insert(c) {
                            new.push(
                                lits.iter()
                                    .copied()
                                    .filter(|&l| self.value(l) == 0)
                                    .collect(),
                            );
                        }
                    }
                    for clause in new {
                        if env.clauses.len() >= max_clauses {
                            break 'depth;
                        }
                        let fresh = clause.iter().filter(|l| map[l.vidx()] == u32::MAX).count();
                        if env.vars.len() + fresh > max_vars {
                            continue;
                        }
                        for &l in &clause {
                            if map[l.vidx()] == u32::MAX {
                                map[l.vidx()] = env.vars.len() as u32;
                                env.vars.push(l.var());
                                next_frontier.push(l.var());
                            }
                        }
                        env.clauses.push(clause);
                    }
                }
            }
            frontier = next_frontier;
        }
        // Map clauses to local literals.
        for clause in &mut env.clauses {
            for l in clause.iter_mut() {
                *l = Lit::new(map[l.vidx()], l.negated());
            }
        }
        env
    }

    /// Add Kitten's new learned clauses (mapped to global literals) to the
    /// proof.
    fn flush_kitten_lemmas(
        &mut self,
        kitten: &Kitten,
        flushed: &mut usize,
        env: &Environment,
        added: &mut Vec<Vec<Lit>>,
    ) {
        if self.proof.is_none() {
            *flushed = kitten.learned.len();
            return;
        }
        for lemma in &kitten.learned[*flushed..] {
            let global: Vec<Lit> = lemma
                .iter()
                .map(|l| Lit::new(env.vars[l.vidx()], l.negated()))
                .collect();
            self.proof.as_mut().unwrap().add(&global);
            added.push(global);
        }
        *flushed = kitten.learned.len();
    }

    fn sweep_environment(&mut self, env: &Environment) {
        let n = env.vars.len();
        let mut kitten = Kitten::new(n);
        for c in &env.clauses {
            kitten.add_clause(c);
        }
        let tick_limit = self.opts.sweepticks;
        let mut flushed = 0;
        let mut lemmas: Vec<Vec<Lit>> = Vec::new();
        let start_ticks = kitten.ticks;
        let res = kitten.solve(&[], tick_limit);
        if res == KittenResult::Unsat {
            // The environment (hence the formula) is unsatisfiable.
            self.flush_kitten_lemmas(&kitten, &mut flushed, env, &mut lemmas);
            self.mark_inconsistent();
            return;
        }
        if res != KittenResult::Sat {
            self.stats.sweep_ticks += kitten.ticks - start_ticks;
            return;
        }
        let mut model = Model::new(&kitten, env, n);
        // Backbone candidates: literals true in all models so far.
        let mut backbone: Vec<Lit> = (0..n as u32).map(|v| model.true_lit(v)).collect();
        // Partition of literals which are equal in all models so far.
        let mut partition: Vec<Vec<Lit>> = vec![backbone.clone()];
        model.flip_refine(&mut backbone, &mut partition);
        let mut solves = 0;
        let max_solves = self.opts.sweepmaxsolves as usize;
        // Backbone.
        while let Some(lit) = backbone.pop() {
            if solves >= max_solves || self.inconsistent {
                break;
            }
            let global = Lit::new(env.vars[lit.vidx()], lit.negated());
            if self.value(global) != 0 {
                continue;
            }
            solves += 1;
            match kitten.solve(&[!lit], tick_limit) {
                KittenResult::Unsat => {
                    self.flush_kitten_lemmas(&kitten, &mut flushed, env, &mut lemmas);
                    if let Some(p) = self.proof.as_mut() {
                        p.add(&[global]);
                    }
                    if kitten.is_inconsistent() {
                        self.mark_inconsistent();
                        break;
                    }
                    self.assign_unit(global);
                    self.stats.sweep_units += 1;
                    kitten.add_clause(&[lit]);
                    for class in partition.iter_mut() {
                        class.retain(|l| l.var() != lit.var());
                    }
                }
                KittenResult::Sat => {
                    model.update(&kitten);
                    model.refine(&mut backbone, &mut partition);
                    model.flip_refine(&mut backbone, &mut partition);
                }
                KittenResult::Unknown => {}
            }
        }
        // Equivalences within classes.
        partition.retain(|c| c.len() > 1);
        while let Some(class) = partition.last() {
            if solves + 2 > max_solves || self.inconsistent {
                break;
            }
            if class.len() < 2 {
                partition.pop();
                continue;
            }
            let lit = class[class.len() - 2];
            let other = class[class.len() - 1];
            let g_lit = Lit::new(env.vars[lit.vidx()], lit.negated());
            let g_other = Lit::new(env.vars[other.vidx()], other.negated());
            if self.value(g_lit) != 0 || self.value(g_other) != 0 {
                partition.last_mut().unwrap().pop();
                continue;
            }
            let mut proven = true;
            let mut refined = false;
            for (a, b) in [(lit, !other), (!lit, other)] {
                solves += 1;
                match kitten.solve(&[a, b], tick_limit) {
                    KittenResult::Unsat => {}
                    KittenResult::Sat => {
                        model.update(&kitten);
                        model.refine(&mut backbone, &mut partition);
                        model.flip_refine(&mut backbone, &mut partition);
                        partition.retain(|c| c.len() > 1);
                        proven = false;
                        refined = true;
                        break;
                    }
                    KittenResult::Unknown => {
                        proven = false;
                        break;
                    }
                }
            }
            if refined {
                continue;
            }
            // Proven or given up: `other` leaves the class.
            partition.last_mut().unwrap().pop();
            if !proven {
                continue;
            }
            self.flush_kitten_lemmas(&kitten, &mut flushed, env, &mut lemmas);
            if let Some(p) = self.proof.as_mut() {
                p.add(&[!g_lit, g_other]);
                p.add(&[g_lit, !g_other]);
            }
            self.new_binary(!g_lit, g_other);
            self.new_binary(g_lit, !g_other);
            self.stats.sweep_equivalences += 1;
        }
        self.stats.sweep_ticks += kitten.ticks - start_ticks + model.ticks;
        if let Some(p) = self.proof.as_mut() {
            for lemma in &lemmas {
                if lemma.len() > 1 {
                    p.delete(lemma);
                }
            }
        }
    }
}

/// The current model of an environment with per-clause true-literal counts
/// for cheap flipping.
struct Model<'a> {
    env: &'a Environment,
    value: Vec<bool>,
    count: Vec<u32>,
    occs: Vec<Vec<u32>>,
    ticks: u64,
}

impl<'a> Model<'a> {
    fn new(kitten: &Kitten, env: &'a Environment, n: usize) -> Self {
        let mut occs = vec![Vec::new(); 2 * n];
        for (i, c) in env.clauses.iter().enumerate() {
            for &l in c {
                occs[l.idx()].push(i as u32);
            }
        }
        let mut m = Model {
            env,
            value: vec![false; n],
            count: vec![0; env.clauses.len()],
            occs,
            ticks: 0,
        };
        m.update(kitten);
        m
    }

    fn update(&mut self, kitten: &Kitten) {
        self.ticks += 1 + (self.value.len() + 2 * self.count.len()) as u64 / 8;
        for v in 0..self.value.len() {
            self.value[v] = kitten.model_value(Lit::new(v as u32, false));
        }
        for (i, c) in self.env.clauses.iter().enumerate() {
            self.count[i] = c.iter().filter(|&&l| self.is_true(l)).count() as u32;
        }
    }

    fn is_true(&self, l: Lit) -> bool {
        self.value[l.vidx()] != l.negated()
    }

    fn true_lit(&self, v: u32) -> Lit {
        Lit::new(v, !self.value[v as usize])
    }

    /// Remove candidates contradicted by the current model.
    fn refine(&self, backbone: &mut Vec<Lit>, partition: &mut Vec<Vec<Lit>>) {
        backbone.retain(|&l| self.is_true(l));
        let mut split: Vec<Vec<Lit>> = Vec::new();
        for class in partition.iter_mut() {
            let (t, f): (Vec<Lit>, Vec<Lit>) = class.iter().partition(|&&l| self.is_true(l));
            *class = t;
            if f.len() > 1 {
                split.push(f);
            }
        }
        partition.extend(split);
        partition.retain(|c| c.len() > 1);
    }

    /// Flip variables whose flip keeps the model satisfying; each flip
    /// refutes the variable as backbone and separates it from its class.
    fn flip_refine(&mut self, backbone: &mut Vec<Lit>, partition: &mut Vec<Vec<Lit>>) {
        self.ticks += 1 + self.value.len() as u64 / 8;
        let mut flipped = vec![false; self.value.len()];
        let mut any = false;
        for v in 0..self.value.len() {
            let t = self.true_lit(v as u32);
            if self.occs[t.idx()]
                .iter()
                .any(|&c| self.count[c as usize] == 1)
            {
                continue;
            }
            for &c in &self.occs[t.idx()] {
                self.count[c as usize] -= 1;
            }
            for &c in &self.occs[(!t).idx()] {
                self.count[c as usize] += 1;
            }
            self.value[v] = !self.value[v];
            flipped[v] = true;
            any = true;
        }
        if !any {
            return;
        }
        backbone.retain(|l| !flipped[l.vidx()]);
        for class in partition.iter_mut() {
            class.retain(|l| !flipped[l.vidx()]);
        }
        partition.retain(|c| c.len() > 1);
    }
}
