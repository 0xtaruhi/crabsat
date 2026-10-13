//! Solver state and clause database management.

use crate::arena::{Arena, CRef, INVALID_REF};
use crate::ema::{Averages, Reluctant};
use crate::heap::Heap;
use crate::options::Options;
use crate::proof::Proof;
use crate::queue::Queue;
use crate::stats::Stats;
use crate::types::{Lit, SolveResult, Var};
use crate::watch::{self, WatchList};

/// Reason of a decision.
pub const DECISION_REASON: u32 = u32::MAX;
/// Reason of a root-level (fixed) assignment.
pub const UNIT_REASON: u32 = u32::MAX - 1;

pub const INVALID_LEVEL: u32 = u32::MAX;

// `Assigned::flags` bits.
pub const ANALYZED: u8 = 1;
pub const BINARY: u8 = 2;
pub const POISONED: u8 = 4;
pub const REMOVABLE: u8 = 8;
pub const SHRINKABLE: u8 = 16;

// `Solver::flags` bits (per variable).
pub const ELIMINATED: u8 = 1;
/// Candidate for variable elimination.
pub const ELIMINATE: u8 = 2;
/// Candidate for subsumption.
pub const SUBSUME: u8 = 4;
/// Already used as root of a sweeping environment.
pub const SWEPT: u8 = 8;

/// Tag of the witness literal in the extension stack.
pub const WITNESS: u32 = 1 << 31;

/// Per-variable assignment information (Kissat `assigned`).
#[derive(Copy, Clone, Default)]
pub struct Assigned {
    pub level: u32,
    pub trail: u32,
    /// Clause reference, or for binary reasons the other literal.
    pub reason: u32,
    pub flags: u8,
}

impl Assigned {
    #[inline(always)]
    pub fn has(&self, f: u8) -> bool {
        self.flags & f != 0
    }
}

/// Decision level frame.
#[derive(Copy, Clone, Default)]
pub struct Frame {
    pub decision: Lit,
    pub trail: u32,
    pub used: u32,
    pub promote: bool,
}

#[derive(Default)]
pub struct Phases {
    pub saved: Vec<i8>,
    pub target: Vec<i8>,
    pub best: Vec<i8>,
}

/// Conflict reported by propagation.
#[derive(Copy, Clone, Debug)]
pub enum Conflict {
    Binary(Lit, Lit),
    Large(CRef),
}

#[derive(Default)]
pub struct Limits {
    pub conflicts: Option<u64>,
    pub decisions: Option<u64>,
    pub mode_count: u64,
    pub mode_ticks: u64,
    pub mode_conflicts: u64,
    pub reduce_conflicts: u64,
    pub rephase_conflicts: u64,
    pub restart_conflicts: u64,
    pub glue_conflicts: u64,
    pub glue_interval: u64,
    pub eliminate_conflicts: u64,
    pub eliminate_variables: u64,
    pub subsume_variables: u64,
    pub probe_conflicts: u64,
    pub factor_marked: u64,
    pub reorder_conflicts: u64,
    pub randec_conflicts: u64,
}

#[derive(Default, Clone, Copy)]
pub struct Delay {
    pub count: u32,
    pub current: u32,
}

impl Delay {
    pub fn delaying(&mut self) -> bool {
        if self.count > 0 {
            self.count -= 1;
            true
        } else {
            false
        }
    }
    pub fn bump(&mut self) {
        self.current = self.current.saturating_add(1);
        self.count = self.current;
    }
    pub fn reduce(&mut self) {
        if self.current > 0 {
            self.current /= 2;
            self.count = self.current;
        }
    }
}

pub struct Solver {
    pub opts: Options,
    pub vars: usize,

    // Assignment.
    pub values: Vec<i8>,
    pub assigned: Vec<Assigned>,
    pub trail: Vec<Lit>,
    pub propagated: usize,
    pub frames: Vec<Frame>,
    pub level: u32,
    pub unassigned: u32,
    pub inconsistent: bool,
    pub iterating: bool,
    /// Root-level units not yet written to the proof.
    pub pending_units: Vec<Lit>,

    // Clauses.
    pub arena: Arena,
    pub watches: Vec<WatchList>,
    pub delayed: Vec<u32>,
    pub first_reducible: CRef,
    pub last_learned: Vec<CRef>,
    pub fixed_at_last_collect: u64,

    // Simplification.
    pub flags: Vec<u8>,
    /// Per variable: bit 0/1 = positive/negative literal is a factor
    /// candidate (was added in a new irredundant clause).
    pub factor_flags: Vec<u8>,
    /// Extension stack for model reconstruction: groups of a witness
    /// literal (tagged with `WITNESS`) followed by the clause literals.
    pub extension: Vec<u32>,
    pub eliminated: u32,
    pub elimination_bound: u32,
    pub dense: bool,
    /// Probing mode: no conflict counting, phase saving or search ticks.
    pub probing: bool,
    /// Warming up phases: conflicts are ignored and not counted.
    pub warming: bool,
    /// Clause which must not propagate (vivification).
    pub ignore: CRef,
    pub last_eliminate_ticks: u64,
    pub last_probe_ticks: u64,
    pub last_walk_ticks: u64,
    /// Remaining conflicts of the current random decision sequence.
    pub randec: u64,
    pub random: u64,
    pub last_reduce_conflicts: u64,

    // Heuristics.
    pub stable: bool,
    pub phases: Phases,
    pub target_assigned: u32,
    pub best_assigned: u32,
    pub heap: Heap,
    pub scinc: f64,
    pub queue: Queue,
    pub averages: [Averages; 2],
    pub reluctant: Reluctant,
    pub tier1: [u32; 2],
    pub tier2: [u32; 2],
    pub delay_bumpreasons: Delay,
    pub delay_congruence: Delay,
    pub delay_sweep: Delay,
    pub delay_vivifyirr: Delay,
    pub mode_ticks: u64,
    pub mode_start: f64,

    // Analysis scratch space.
    pub clause: Vec<Lit>,
    pub levels: Vec<u32>,
    pub analyzed: Vec<Var>,
    pub removable: Vec<Var>,
    pub poisoned: Vec<Var>,
    pub shrinkable: Vec<Var>,
    pub minimize_stack: Vec<Var>,
    pub promote_levels: Vec<u32>,
    pub marks: Vec<i8>,
    pub antecedent_size: u32,
    pub resolvent_size: u32,

    pub limits: Limits,
    pub stats: Stats,
    pub proof: Option<Proof>,
    pub start_time: std::time::Instant,
    pub terminate: Option<std::sync::Arc<std::sync::atomic::AtomicBool>>,
    pub shared: Option<std::sync::Arc<crate::share::Shared>>,
    pub exported: usize,
    pub imported: usize,
    pub replay: Option<Vec<(u64, u64, Vec<Lit>)>>,
    pub root_log: Option<Vec<Lit>>,
    /// Variables in order of their first occurrence in added clauses.
    pub first_seen: Vec<Var>,
    pub seen: Vec<bool>,
    pub activated: u64,
    /// Number of external variables (original plus fresh ones).
    pub evars: usize,
    /// External variable -> internal (positive) literal, or `INVALID` if the
    /// variable was removed by compaction.
    pub e2i: Vec<Lit>,
    /// Internal variable -> external variable.
    pub i2e: Vec<u32>,
    /// Values of external variables fixed at the root and compacted away.
    pub ext_fixed: Vec<i8>,
}

impl Solver {
    pub fn new(opts: Options) -> Solver {
        let mut s = Solver {
            opts,
            vars: 0,
            values: Vec::new(),
            assigned: Vec::new(),
            trail: Vec::new(),
            propagated: 0,
            frames: vec![Frame::default()],
            level: 0,
            unassigned: 0,
            inconsistent: false,
            iterating: false,
            pending_units: Vec::new(),
            arena: Arena::default(),
            watches: Vec::new(),
            delayed: Vec::new(),
            first_reducible: INVALID_REF,
            last_learned: Vec::new(),
            fixed_at_last_collect: 0,
            flags: Vec::new(),
            factor_flags: Vec::new(),
            extension: Vec::new(),
            eliminated: 0,
            elimination_bound: 0,
            dense: false,
            probing: false,
            warming: false,
            ignore: INVALID_REF,
            last_eliminate_ticks: 0,
            last_probe_ticks: 0,
            last_walk_ticks: 0,
            randec: 0,
            random: 0,
            last_reduce_conflicts: u64::MAX,
            stable: false,
            phases: Phases::default(),
            target_assigned: 0,
            best_assigned: 0,
            heap: Heap::default(),
            scinc: 1.0,
            queue: Queue::default(),
            averages: [Averages::default(); 2],
            reluctant: Reluctant::default(),
            tier1: [0; 2],
            tier2: [0; 2],
            delay_bumpreasons: Delay::default(),
            delay_congruence: Delay::default(),
            delay_sweep: Delay::default(),
            delay_vivifyirr: Delay::default(),
            mode_ticks: 0,
            mode_start: 0.0,
            clause: Vec::new(),
            levels: Vec::new(),
            analyzed: Vec::new(),
            removable: Vec::new(),
            poisoned: Vec::new(),
            shrinkable: Vec::new(),
            minimize_stack: Vec::new(),
            promote_levels: Vec::new(),
            marks: Vec::new(),
            antecedent_size: 0,
            resolvent_size: 0,
            limits: Limits::default(),
            stats: Stats::default(),
            proof: None,
            start_time: std::time::Instant::now(),
            terminate: None,
            shared: None,
            exported: 0,
            imported: 0,
            replay: None,
            root_log: std::env::var_os("CRABSAT_CHECK_DB").map(|_| Vec::new()),
            first_seen: Vec::new(),
            seen: Vec::new(),
            activated: 0,
            evars: 0,
            e2i: Vec::new(),
            i2e: Vec::new(),
            ext_fixed: Vec::new(),
        };
        s.last_learned = vec![INVALID_REF; s.opts.eagersubsume as usize];
        s.random = s.opts.seed;
        s
    }

    pub fn set_proof(&mut self, mut proof: Proof) {
        proof.map = self.i2e.clone();
        self.proof = Some(proof);
    }

    /// Make sure external variables `0..evars` exist.
    pub fn reserve_vars(&mut self, evars: usize) {
        if evars <= self.evars {
            return;
        }
        let new = evars - self.evars;
        let first = self.vars;
        self.grow_internal(first + new);
        for k in 0..new {
            let i = (first + k) as u32;
            let e = self.evars as u32;
            self.evars += 1;
            self.e2i.push(Lit::new(i, false));
            self.i2e.push(e);
            self.ext_fixed.push(0);
            if let Some(p) = self.proof.as_mut() {
                p.map.push(e);
            }
        }
    }

    /// A fresh variable (internal and external), e.g. for factorization.
    pub fn new_var(&mut self) -> Var {
        let v = self.vars as Var;
        self.reserve_vars(self.evars + 1);
        v
    }

    /// The external literal of an internal literal.
    #[inline]
    pub fn external(&self, lit: Lit) -> Lit {
        Lit::new(self.i2e[lit.vidx()], lit.negated())
    }

    /// The internal literal of an external literal, if the variable was not
    /// compacted away.
    #[inline]
    pub fn internal(&self, lit: Lit) -> Option<Lit> {
        let i = *self.e2i.get(lit.vidx())?;
        (i != Lit::INVALID).then(|| if lit.negated() { !i } else { i })
    }

    /// Make sure internal variables `0..vars` exist.
    fn grow_internal(&mut self, vars: usize) {
        if vars <= self.vars {
            return;
        }
        let old = self.vars;
        self.vars = vars;
        self.values.resize(2 * vars, 0);
        self.marks.resize(2 * vars, 0);
        self.watches.resize_with(2 * vars, Vec::new);
        self.assigned.resize(vars, Assigned::default());
        self.flags.resize(vars, ELIMINATE | SUBSUME);
        self.factor_flags.resize(vars, 3);
        self.stats.literals_factor += 2 * (vars - old) as u64;
        self.stats.variables_eliminate += (vars - old) as u64;
        self.stats.variables_subsume += (vars - old) as u64;
        let initial = if self.opts.phase { 1 } else { -1 };
        self.phases.saved.resize(vars, initial);
        self.phases.target.resize(vars, 0);
        self.phases.best.resize(vars, 0);
        self.heap.resize(vars);
        self.trail.reserve(vars - old);
        for v in old..vars {
            self.unassigned += 1;
            self.heap.push(v as Var);
            self.queue.enqueue(v as Var, true);
        }
    }

    #[inline(always)]
    pub fn value(&self, lit: Lit) -> i8 {
        self.values[lit.idx()]
    }

    #[inline(always)]
    pub fn level_of(&self, lit: Lit) -> u32 {
        self.assigned[lit.vidx()].level
    }

    #[inline(always)]
    pub fn fixed(&self, lit: Lit) -> i8 {
        let v = self.values[lit.idx()];
        if v != 0 && self.assigned[lit.vidx()].level == 0 { v } else { 0 }
    }

    pub fn assigned_count(&self) -> u32 {
        self.vars as u32 - self.unassigned
    }

    /// After variables were eliminated, recount the trail heights of the
    /// target and best phases over active variables (Kissat `compact.c`).
    pub fn recount_phase_heights(&mut self) {
        let mut target = 0;
        let mut best = 0;
        for v in 0..self.vars {
            if self.flags[v] & ELIMINATED != 0 {
                continue;
            }
            target += (self.phases.target[v] != 0) as u32;
            best += (self.phases.best[v] != 0) as u32;
        }
        self.target_assigned = target;
        self.best_assigned = best;
    }

    /// Assign `lit` (slow path, outside of propagation).
    pub fn assign(&mut self, lit: Lit, level: u32, binary: bool, mut reason: u32) {
        debug_assert_eq!(self.values[lit.idx()], 0);
        let mut flags = if binary { BINARY } else { 0 };
        if level == 0 {
            if self.root_log.is_some() {
                self.root_log.as_mut().unwrap().push(lit);
            }
            if reason != UNIT_REASON {
                self.pending_units.push(lit);
                reason = UNIT_REASON;
            }
            flags = 0;
            self.stats.units += 1;
        }
        self.values[lit.idx()] = 1;
        self.values[(!lit).idx()] = -1;
        self.unassigned -= 1;
        if !self.probing {
            self.phases.saved[lit.vidx()] = if lit.negated() { -1 } else { 1 };
        }
        self.assigned[lit.vidx()] =
            Assigned { level, trail: self.trail.len() as u32, reason, flags };
        self.trail.push(lit);
    }

    /// Assign a learned or original unit at the root level.
    pub fn assign_unit(&mut self, lit: Lit) {
        self.assign(lit, 0, false, UNIT_REASON);
    }

    /// Assign a learned unit and add it to the proof.
    pub fn learned_unit(&mut self, lit: Lit) {
        self.assign_unit(lit);
        if let Some(p) = self.proof.as_mut() {
            p.add(&[lit]);
        }
    }

    /// Assign `lit` with a binary reason `other`.
    pub fn assign_binary(&mut self, lit: Lit, other: Lit) {
        let level = self.level_of(other);
        self.assign(lit, level, true, other.0);
    }

    /// Assign `lit` with a large reason clause.
    pub fn assign_reference(&mut self, lit: Lit, c: CRef) {
        let mut level = 0;
        for &other in self.arena.lits(c) {
            if other != lit {
                debug_assert!(self.value(other) < 0);
                level = level.max(self.level_of(other));
            }
        }
        self.assign(lit, level, false, c);
    }

    pub fn assign_decision(&mut self, lit: Lit) {
        self.level += 1;
        self.frames.push(Frame {
            decision: lit,
            trail: self.trail.len() as u32,
            used: 0,
            promote: false,
        });
        self.assign(lit, self.level, false, DECISION_REASON);
    }

    pub fn flush_pending_units(&mut self) {
        if let Some(log) = self.root_log.as_mut() {
            log.extend_from_slice(&self.pending_units);
        }
        if let Some(proof) = self.proof.as_mut() {
            for &lit in &self.pending_units {
                proof.add(&[lit]);
            }
        }
        self.pending_units.clear();
    }

    pub fn mark_inconsistent(&mut self) {
        if self.inconsistent {
            return;
        }
        self.inconsistent = true;
        self.flush_pending_units();
        if let Some(p) = self.proof.as_mut() {
            p.add(&[]);
        }
    }

    // ------------------------------------------------------------------
    // Clause creation and deletion.

    pub fn watch_binary(&mut self, a: Lit, b: Lit) {
        watch::push_binary(&mut self.watches[a.idx()], b);
        watch::push_binary(&mut self.watches[b.idx()], a);
    }

    pub fn watch_clause(&mut self, c: CRef) {
        let lits = self.arena.lits(c);
        let (l0, l1) = (lits[0], lits[1]);
        watch::push_large(&mut self.watches[l0.idx()], l1, c);
        watch::push_large(&mut self.watches[l1.idx()], l0, c);
    }

    pub fn unwatch_clause(&mut self, c: CRef) {
        let lits = self.arena.lits(c);
        let (l0, l1) = (lits[0], lits[1]);
        watch::remove_large(&mut self.watches[l0.idx()], c);
        watch::remove_large(&mut self.watches[l1.idx()], c);
    }

    /// A literal was added in a new irredundant clause.
    #[inline]
    pub fn mark_added_lit(&mut self, lit: Lit) {
        let bit = 1 << lit.negated() as u8;
        let f = &mut self.factor_flags[lit.vidx()];
        if *f & bit == 0 {
            *f |= bit;
            self.stats.literals_factor += 1;
        }
        self.mark_added_var(lit.vidx());
    }

    pub fn new_binary(&mut self, a: Lit, b: Lit) {
        self.mark_added_lit(a);
        self.mark_added_lit(b);
        self.stats.clauses_binary += 1;
        self.watch_binary(a, b);
    }

    /// A clause with this variable was removed: it becomes an elimination
    /// candidate again.
    #[inline]
    pub fn mark_removed_var(&mut self, v: usize) {
        if self.flags[v] & ELIMINATE == 0 {
            self.flags[v] |= ELIMINATE;
            self.stats.variables_eliminate += 1;
        }
    }

    /// A clause with this variable was added: it becomes a subsumption
    /// candidate again.
    #[inline]
    pub fn mark_added_var(&mut self, v: usize) {
        if self.flags[v] & SUBSUME == 0 {
            self.flags[v] |= SUBSUME;
            self.stats.variables_subsume += 1;
        }
    }

    #[inline]
    pub fn active(&self, v: usize) -> bool {
        self.flags[v] & ELIMINATED == 0 && self.fixed(Lit::new(v as Var, false)) == 0
    }

    pub fn delete_binary(&mut self, a: Lit, b: Lit, proof: bool) {
        self.trace("delete-binary", &[a, b]);
        self.mark_removed_var(a.vidx());
        self.mark_removed_var(b.vidx());
        self.stats.clauses_binary -= 1;
        watch::remove_binary(&mut self.watches[a.idx()], b);
        watch::remove_binary(&mut self.watches[b.idx()], a);
        if proof {
            if let Some(p) = self.proof.as_mut() {
                p.delete(&[a, b]);
            }
        }
    }

    /// Add a large clause to the arena and watch it.
    pub fn new_large(&mut self, lits: &[Lit], redundant: bool, glue: u32) -> CRef {
        let c = self.arena.alloc(lits, redundant, glue);
        if redundant {
            self.stats.clauses_redundant += 1;
            if self.first_reducible == INVALID_REF {
                self.first_reducible = c;
            }
        } else {
            self.stats.clauses_irredundant += 1;
            for &l in lits {
                self.mark_added_lit(l);
            }
        }
        self.watch_clause(c);
        c
    }

    /// Debugging: report events on clauses whose literals are a subset of
    /// the clause given in `CRABSAT_TRACE` (comma separated DIMACS).
    pub fn trace(&self, event: &str, lits: &[Lit]) {
        static TARGET: std::sync::OnceLock<Option<Vec<i32>>> = std::sync::OnceLock::new();
        let target = TARGET.get_or_init(|| {
            std::env::var_os("CRABSAT_TRACE").map(|spec| {
                spec.to_string_lossy().split(',').map(|x| x.trim().parse().unwrap()).collect()
            })
        });
        let Some(target) = target else { return };
        if lits.iter().all(|l| target.contains(&self.external(*l).to_dimacs())) {
            let d: Vec<i32> = lits.iter().map(|l| self.external(*l).to_dimacs()).collect();
            eprintln!(
                "TRACE {event} {d:?} conflicts {} dense {} probing {} level {}",
                self.stats.conflicts, self.dense, self.probing, self.level
            );
        }
    }

    /// Mark a large clause as garbage (removed at the next collection).
    pub fn mark_garbage(&mut self, c: CRef) {
        self.trace("garbage", self.arena.lits(c));
        debug_assert!(!self.arena.garbage(c));
        if let Some(p) = self.proof.as_mut() {
            p.delete(self.arena.lits(c));
        }
        if self.arena.redundant(c) {
            self.stats.clauses_redundant -= 1;
        } else {
            self.stats.clauses_irredundant -= 1;
            for i in 0..self.arena.size(c) {
                let v = self.arena.lits(c)[i].vidx();
                self.mark_removed_var(v);
            }
        }
        self.arena.set_garbage(c, true);
    }

    /// Add an original clause given as DIMACS literals.
    pub fn add_clause_dimacs(&mut self, dimacs: &[i32]) {
        let mut lits: Vec<Lit> = Vec::with_capacity(dimacs.len());
        for &d in dimacs {
            let e = Lit::from_dimacs(d);
            self.reserve_vars(e.vidx() + 1);
            match self.internal(e) {
                Some(l) => lits.push(l),
                None => {
                    // Fixed at the root and compacted away.
                    let v = self.ext_fixed[e.vidx()];
                    assert!(v != 0, "clauses on eliminated variables are not supported");
                    if (v > 0) != e.negated() {
                        return; // satisfied
                    }
                }
            }
        }
        self.add_clause(&lits);
    }

    /// Add an original (irredundant) clause.  Must be called at level 0.
    pub fn add_clause(&mut self, lits: &[Lit]) {
        assert_eq!(self.level, 0, "clauses can only be added at the root level");
        if let Some(max) = lits.iter().map(|l| l.vidx()).max() {
            assert!(max < self.vars, "unknown internal variable");
        }
        if self.seen.len() < self.vars {
            self.seen.resize(self.vars, false);
        }
        for &l in lits {
            if !self.seen[l.vidx()] {
                self.seen[l.vidx()] = true;
                self.first_seen.push(l.var());
            }
        }
        if self.inconsistent {
            return;
        }
        // Remove duplicates and falsified literals, detect tautologies and
        // satisfied clauses.  Marks: 1 = literal seen.
        let mut simplified: Vec<Lit> = Vec::with_capacity(lits.len());
        let mut satisfied = false;
        for &lit in lits {
            if self.marks[lit.idx()] != 0 {
                continue;
            }
            if self.marks[(!lit).idx()] != 0 {
                satisfied = true; // tautology
                break;
            }
            let v = self.value(lit);
            if v > 0 {
                satisfied = true;
                break;
            }
            self.marks[lit.idx()] = 1;
            if v < 0 {
                continue;
            }
            simplified.push(lit);
        }
        for &lit in lits {
            self.marks[lit.idx()] = 0;
        }
        if satisfied {
            return;
        }
        if simplified.len() != lits.len() {
            if let Some(p) = self.proof.as_mut() {
                p.add(&simplified);
                p.delete(lits);
            }
        }
        match simplified.len() {
            0 => self.mark_inconsistent(),
            // Original units need no proof line (a simplified one was added).
            1 => self.assign_unit(simplified[0]),
            2 => self.new_binary(simplified[0], simplified[1]),
            _ => {
                self.new_large(&simplified, false, 0);
            }
        }
    }

    /// The satisfying assignment in DIMACS form (1-based, signed), with
    /// eliminated variables reconstructed from the extension stack.
    pub fn model(&self) -> Vec<i32> {
        let mut value: Vec<bool> = (0..self.evars).map(|e| self.external_value(e)).collect();
        let ext = &self.extension;
        let mut end = ext.len();
        while end > 0 {
            // The group starts at the witness (the last tagged entry).
            let mut start = end - 1;
            while ext[start] & WITNESS == 0 {
                start -= 1;
            }
            let satisfied = ext[start..end].iter().any(|&e| {
                let l = Lit(e & !WITNESS);
                value[l.vidx()] != l.negated()
            });
            if !satisfied {
                let w = Lit(ext[start] & !WITNESS);
                value[w.vidx()] = !w.negated();
            }
            end = start;
        }
        value
            .iter()
            .enumerate()
            .map(|(v, &b)| if b { v as i32 + 1 } else { -(v as i32 + 1) })
            .collect()
    }

    /// Current value of an external variable (before reconstruction).
    fn external_value(&self, e: usize) -> bool {
        match self.e2i[e] {
            Lit::INVALID => self.ext_fixed[e] > 0,
            i => self.values[i.idx()] > 0,
        }
    }

    /// A clause of the current clause database falsified (or not
    /// satisfied) by the current full assignment, for debugging.
    pub fn unsatisfied_clause(&self) -> Option<Vec<Lit>> {
        for idx in 0..self.watches.len() {
            let lit = Lit(idx as u32);
            for w in watch::iter(&self.watches[idx]) {
                if let watch::Watch::Binary(other) = w {
                    if self.value(lit) <= 0 && self.value(other) <= 0 {
                        return Some(vec![lit, other]);
                    }
                }
            }
        }
        let mut c = 0;
        while (c as usize) < self.arena.len() {
            if !self.arena.garbage(c) && !self.arena.lits(c).iter().any(|&l| self.value(l) > 0) {
                return Some(self.arena.lits(c).to_vec());
            }
            c = self.arena.next(c);
        }
        None
    }

    /// Debugging: replay model reconstruction and report the flips of
    /// variables of `target` together with the witness clauses.
    pub fn debug_reconstruct(&self, target: &[Lit]) {
        let mut value: Vec<bool> = (0..self.evars).map(|e| self.external_value(e)).collect();
        let ext = &self.extension;
        let mut end = ext.len();
        while end > 0 {
            let mut start = end - 1;
            while ext[start] & WITNESS == 0 {
                start -= 1;
            }
            let clause: Vec<Lit> = ext[start..end].iter().map(|&e| Lit(e & !WITNESS)).collect();
            let satisfied = clause.iter().any(|l| value[l.vidx()] != l.negated());
            if !satisfied {
                let w = clause[0];
                value[w.vidx()] = !w.negated();
                if target.iter().any(|t| t.var() == w.var()) {
                    let d: Vec<String> = clause.iter().map(|l| format!("{l}")).collect();
                    let tsat = target.iter().any(|l| value[l.vidx()] != l.negated());
                    eprintln!("FLIP {} by {:?} at {} -> target satisfied {}", w, d, start, tsat);
                }
            }
            end = start;
        }
    }

    /// Push a clause with witness literal `witness` (which must be in the
    /// clause) onto the extension stack.
    pub fn push_extension(&mut self, witness: Lit, lits: &[Lit]) {
        self.trace(&format!("extension(witness {witness})"), lits);
        self.extension.push(self.external(witness).0 | WITNESS);
        for &l in lits {
            if l != witness {
                self.extension.push(self.external(l).0);
            }
        }
    }

    pub fn solve(&mut self) -> SolveResult {
        let res = self.search();
        if let Some(log) = &self.root_log {
            for &l in log {
                if self.value(l) <= 0 || self.flags[l.vidx()] & ELIMINATED != 0 {
                    eprintln!(
                        "ROOT VIOLATION {} value {} level {} flags {}",
                        l,
                        self.value(l),
                        self.assigned[l.vidx()].level,
                        self.flags[l.vidx()]
                    );
                }
            }
        }
        if res == SolveResult::Sat && std::env::var_os("CRABSAT_CHECK_DB").is_some() {
            if let Some(c) = self.unsatisfied_clause() {
                let info: Vec<String> = c
                    .iter()
                    .map(|&l| {
                        let a = self.assigned[l.vidx()];
                        format!(
                            "{}@{}:{}{}",
                            l,
                            a.level,
                            self.value(l),
                            if self.flags[l.vidx()] & ELIMINATED != 0 { "E" } else { "" }
                        )
                    })
                    .collect();
                panic!("database clause not satisfied: {info:?} (imported {})", self.stats.imported_units);
            }
        }
        self.flush_pending_units();
        if let Some(p) = self.proof.as_mut() {
            p.flush();
        }
        res
    }

    pub fn terminated(&self) -> bool {
        self.terminate
            .as_ref()
            .is_some_and(|t| t.load(std::sync::atomic::Ordering::Relaxed))
    }

    pub fn seconds(&self) -> f64 {
        self.start_time.elapsed().as_secs_f64()
    }

    pub fn verbose(&self, level: u32) -> bool {
        !self.opts.quiet && self.opts.verbose >= level
    }
}
