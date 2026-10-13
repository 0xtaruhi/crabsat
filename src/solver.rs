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
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

/// Reason of a decision.
pub const DECISION_REASON: u32 = u32::MAX;
/// Reason of a root-level (fixed) assignment.
pub const UNIT_REASON: u32 = u32::MAX - 1;

pub const INVALID_LEVEL: u32 = u32::MAX;

pub use crate::flags::{
    ANALYZED, AssignFlags, BINARY, ELIMINATE, ELIMINATED, POISONED, REMOVABLE, SHRINKABLE, SUBSUME,
    SWEPT, VarFlags,
};

/// Tag of the witness literal in the extension stack.
pub const WITNESS: u32 = 1 << 31;

/// Per-variable assignment information (Kissat `assigned`).
#[derive(Copy, Clone, Default)]
pub struct Assigned {
    pub level: u32,
    pub trail: u32,
    /// Clause reference, or for binary reasons the other literal.
    pub reason: u32,
    pub flags: AssignFlags,
}

impl Assigned {
    #[inline(always)]
    pub(crate) fn has(&self, f: AssignFlags) -> bool {
        self.flags.has(f)
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

#[derive(Default, Clone)]
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

#[derive(Default, Clone)]
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
    pub(crate) fn delaying(&mut self) -> bool {
        if self.count > 0 {
            self.count -= 1;
            true
        } else {
            false
        }
    }
    pub(crate) fn bump(&mut self) {
        self.current = self.current.saturating_add(1);
        self.count = self.current;
    }
    pub(crate) fn reduce(&mut self) {
        if self.current > 0 {
            self.current /= 2;
            self.count = self.current;
        }
    }
}

pub struct Solver {
    pub(crate) opts: Options,
    pub(crate) vars: usize,

    // Assignment.
    pub(crate) values: Vec<i8>,
    pub(crate) assigned: Vec<Assigned>,
    pub(crate) trail: Vec<Lit>,
    pub(crate) propagated: usize,
    pub(crate) frames: Vec<Frame>,
    pub(crate) level: u32,
    pub(crate) unassigned: u32,
    pub(crate) inconsistent: bool,
    pub(crate) iterating: bool,
    /// Root-level units not yet written to the proof.
    pub(crate) pending_units: Vec<Lit>,

    // Clauses.
    pub(crate) arena: Arena,
    pub(crate) watches: Vec<WatchList>,
    pub(crate) delayed: Vec<u32>,
    pub(crate) first_reducible: CRef,
    pub(crate) last_learned: Vec<CRef>,
    pub(crate) fixed_at_last_collect: u64,

    // Simplification.
    pub(crate) flags: Vec<VarFlags>,
    /// Per variable: bit 0/1 = positive/negative literal is a factor
    /// candidate (was added in a new irredundant clause).
    pub(crate) factor_flags: Vec<u8>,
    /// Extension stack for model reconstruction: groups of a witness
    /// literal (tagged with `WITNESS`) followed by the clause literals.
    pub(crate) extension: Vec<u32>,
    pub(crate) eliminated: u32,
    pub(crate) elimination_bound: u32,
    pub(crate) dense: bool,
    /// Probing mode: no conflict counting, phase saving or search ticks.
    pub(crate) probing: bool,
    /// Warming up phases: conflicts are ignored and not counted.
    pub(crate) warming: bool,
    /// Clause which must not propagate (vivification).
    pub(crate) ignore: CRef,
    pub(crate) last_eliminate_ticks: u64,
    pub(crate) last_probe_ticks: u64,
    pub(crate) last_walk_ticks: u64,
    /// Remaining conflicts of the current random decision sequence.
    pub(crate) randec: u64,
    pub(crate) random: u64,
    pub(crate) last_reduce_conflicts: u64,

    // Heuristics.
    pub(crate) stable: bool,
    pub(crate) phases: Phases,
    pub(crate) target_assigned: u32,
    pub(crate) best_assigned: u32,
    pub(crate) heap: Heap,
    pub(crate) scinc: f64,
    pub(crate) queue: Queue,
    pub(crate) averages: [Averages; 2],
    pub(crate) reluctant: Reluctant,
    pub(crate) tier1: [u32; 2],
    pub(crate) tier2: [u32; 2],
    pub(crate) delay_bumpreasons: Delay,
    pub(crate) delay_congruence: Delay,
    pub(crate) delay_sweep: Delay,
    pub(crate) delay_vivifyirr: Delay,
    pub(crate) mode_ticks: u64,
    pub(crate) mode_start: f64,

    // Analysis scratch space.
    pub(crate) clause: Vec<Lit>,
    pub(crate) levels: Vec<u32>,
    pub(crate) analyzed: Vec<Var>,
    pub(crate) removable: Vec<Var>,
    pub(crate) poisoned: Vec<Var>,
    pub(crate) shrinkable: Vec<Var>,
    pub(crate) minimize_stack: Vec<Var>,
    pub(crate) promote_levels: Vec<u32>,
    pub(crate) marks: Vec<i8>,
    pub(crate) antecedent_size: u32,
    pub(crate) resolvent_size: u32,

    pub(crate) limits: Limits,
    pub(crate) stats: Stats,
    pub(crate) proof: Option<Proof>,
    pub(crate) start_time: std::time::Instant,
    pub(crate) terminate: Option<Arc<AtomicBool>>,
    pub(crate) shared: Option<Arc<crate::share::Shared>>,
    pub(crate) exported: usize,
    pub(crate) imported: usize,
    pub(crate) share_id: u32,
    pub(crate) export_buffer: Vec<crate::share::SharedClause>,
    pub(crate) imported_clauses: usize,
    pub(crate) last_share: u64,
    /// Preprocessing (and the lucky phases) already ran.
    pub(crate) presolved: bool,
    /// Assumptions (external literals) for the next solve call.
    pub(crate) assumptions: Vec<Lit>,
    pub(crate) failed_assumptions: Vec<Lit>,
    /// Model of the last satisfiable call in incremental mode.
    pub(crate) last_model: Vec<i32>,
    pub(crate) terminate_cb: Option<crate::incremental::TerminateFn>,
    pub(crate) learn_cb: Option<(usize, crate::incremental::LearnFn)>,
    pub(crate) terminate_calls: std::cell::Cell<u32>,
    /// Variables in order of their first occurrence in added clauses.
    pub(crate) first_seen: Vec<Var>,
    pub(crate) seen: Vec<bool>,
    /// Number of external variables (original plus fresh ones).
    pub(crate) evars: usize,
    /// External variable -> internal (positive) literal, or `INVALID` if the
    /// variable was removed by compaction.
    pub(crate) e2i: Vec<Lit>,
    /// Internal variable -> external variable.
    pub(crate) i2e: Vec<u32>,
    /// Values of external variables fixed at the root and compacted away.
    pub(crate) ext_fixed: Vec<i8>,
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
            share_id: 0,
            export_buffer: Vec::new(),
            imported_clauses: 0,
            last_share: 0,
            presolved: false,
            assumptions: Vec::new(),
            failed_assumptions: Vec::new(),
            last_model: Vec::new(),
            terminate_cb: None,
            learn_cb: None,
            terminate_calls: std::cell::Cell::new(0),
            first_seen: Vec::new(),
            seen: Vec::new(),
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
    pub(crate) fn new_var(&mut self) -> Var {
        let v = self.vars as Var;
        self.reserve_vars(self.evars + 1);
        v
    }

    /// The external literal of an internal literal.
    #[inline]
    pub(crate) fn external(&self, lit: Lit) -> Lit {
        Lit::new(self.i2e[lit.vidx()], lit.negated())
    }

    /// The internal literal of an external literal, if the variable was not
    /// compacted away.
    #[inline]
    pub(crate) fn internal(&self, lit: Lit) -> Option<Lit> {
        let i = *self.e2i.get(lit.vidx())?;
        (i != Lit::INVALID).then(|| if lit.negated() { !i } else { i })
    }

    /// Make sure internal variables `0..vars` exist.
    pub(crate) fn grow_internal(&mut self, vars: usize) {
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
    pub(crate) fn value(&self, lit: Lit) -> i8 {
        self.values[lit.idx()]
    }

    #[inline(always)]
    pub(crate) fn level_of(&self, lit: Lit) -> u32 {
        self.assigned[lit.vidx()].level
    }

    #[inline(always)]
    pub(crate) fn fixed(&self, lit: Lit) -> i8 {
        let v = self.values[lit.idx()];
        if v != 0 && self.assigned[lit.vidx()].level == 0 {
            v
        } else {
            0
        }
    }

    pub(crate) fn assigned_count(&self) -> u32 {
        self.vars as u32 - self.unassigned
    }

    /// After variables were eliminated, recount the trail heights of the
    /// target and best phases over active variables (Kissat `compact.c`).
    pub(crate) fn recount_phase_heights(&mut self) {
        let mut target = 0;
        let mut best = 0;
        for v in 0..self.vars {
            if self.flags[v].has(ELIMINATED) {
                continue;
            }
            target += (self.phases.target[v] != 0) as u32;
            best += (self.phases.best[v] != 0) as u32;
        }
        self.target_assigned = target;
        self.best_assigned = best;
    }

    /// Assign `lit` (slow path, outside of propagation).
    pub(crate) fn assign(&mut self, lit: Lit, level: u32, binary: bool, mut reason: u32) {
        debug_assert_eq!(self.values[lit.idx()], 0);
        let mut flags = if binary { BINARY } else { AssignFlags::EMPTY };
        if level == 0 {
            if reason != UNIT_REASON {
                self.pending_units.push(lit);
                reason = UNIT_REASON;
            }
            flags = AssignFlags::EMPTY;
            self.stats.units += 1;
        }
        self.values[lit.idx()] = 1;
        self.values[(!lit).idx()] = -1;
        self.unassigned -= 1;
        if !self.probing {
            self.phases.saved[lit.vidx()] = if lit.negated() { -1 } else { 1 };
        }
        self.assigned[lit.vidx()] = Assigned {
            level,
            trail: self.trail.len() as u32,
            reason,
            flags,
        };
        self.trail.push(lit);
    }

    /// Assign a learned or original unit at the root level.
    pub(crate) fn assign_unit(&mut self, lit: Lit) {
        self.assign(lit, 0, false, UNIT_REASON);
    }

    /// Assign a learned unit and add it to the proof.
    pub(crate) fn learned_unit(&mut self, lit: Lit) {
        self.assign_unit(lit);
        if let Some(p) = self.proof.as_mut() {
            p.add(&[lit]);
        }
    }

    /// Assign `lit` with a binary reason `other`.
    pub(crate) fn assign_binary(&mut self, lit: Lit, other: Lit) {
        let level = self.level_of(other);
        self.assign(lit, level, true, other.0);
    }

    /// Assign `lit` with a large reason clause.
    pub(crate) fn assign_reference(&mut self, lit: Lit, c: CRef) {
        let mut level = 0;
        for &other in self.arena.lits(c) {
            if other != lit {
                debug_assert!(self.value(other) < 0);
                level = level.max(self.level_of(other));
            }
        }
        self.assign(lit, level, false, c);
    }

    pub(crate) fn assign_decision(&mut self, lit: Lit) {
        self.level += 1;
        self.frames.push(Frame {
            decision: lit,
            trail: self.trail.len() as u32,
            used: 0,
            promote: false,
        });
        self.assign(lit, self.level, false, DECISION_REASON);
    }

    pub(crate) fn flush_pending_units(&mut self) {
        if let Some(proof) = self.proof.as_mut() {
            for &lit in &self.pending_units {
                proof.add(&[lit]);
            }
        }
        self.pending_units.clear();
    }

    pub(crate) fn mark_inconsistent(&mut self) {
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

    pub(crate) fn watch_binary(&mut self, a: Lit, b: Lit) {
        watch::push_binary(&mut self.watches[a.idx()], b);
        watch::push_binary(&mut self.watches[b.idx()], a);
    }

    pub(crate) fn watch_clause(&mut self, c: CRef) {
        let lits = self.arena.lits(c);
        let (l0, l1) = (lits[0], lits[1]);
        watch::push_large(&mut self.watches[l0.idx()], l1, c);
        watch::push_large(&mut self.watches[l1.idx()], l0, c);
    }

    pub(crate) fn unwatch_clause(&mut self, c: CRef) {
        let lits = self.arena.lits(c);
        let (l0, l1) = (lits[0], lits[1]);
        watch::remove_large(&mut self.watches[l0.idx()], c);
        watch::remove_large(&mut self.watches[l1.idx()], c);
    }

    /// A literal was added in a new irredundant clause.
    #[inline]
    pub(crate) fn mark_added_lit(&mut self, lit: Lit) {
        let bit = 1 << lit.negated() as u8;
        let f = &mut self.factor_flags[lit.vidx()];
        if *f & bit == 0 {
            *f |= bit;
            self.stats.literals_factor += 1;
        }
        self.mark_added_var(lit.vidx());
    }

    pub(crate) fn new_binary(&mut self, a: Lit, b: Lit) {
        self.mark_added_lit(a);
        self.mark_added_lit(b);
        self.stats.clauses_binary += 1;
        self.watch_binary(a, b);
    }

    /// A clause with this variable was removed: it becomes an elimination
    /// candidate again.
    #[inline]
    pub(crate) fn mark_removed_var(&mut self, v: usize) {
        if !self.flags[v].has(ELIMINATE) {
            self.flags[v].insert(ELIMINATE);
            self.stats.variables_eliminate += 1;
        }
    }

    /// A clause with this variable was added: it becomes a subsumption
    /// candidate again.
    #[inline]
    pub(crate) fn mark_added_var(&mut self, v: usize) {
        if !self.flags[v].has(SUBSUME) {
            self.flags[v].insert(SUBSUME);
            self.stats.variables_subsume += 1;
        }
    }

    pub(crate) fn delete_binary(&mut self, a: Lit, b: Lit, proof: bool) {
        self.mark_removed_var(a.vidx());
        self.mark_removed_var(b.vidx());
        self.stats.clauses_binary -= 1;
        watch::remove_binary(&mut self.watches[a.idx()], b);
        watch::remove_binary(&mut self.watches[b.idx()], a);
        if proof && let Some(p) = self.proof.as_mut() {
            p.delete(&[a, b]);
        }
    }

    /// Add a large clause to the arena and watch it.
    pub(crate) fn new_large(&mut self, lits: &[Lit], redundant: bool, glue: u32) -> CRef {
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

    /// Mark a large clause as garbage (removed at the next collection).
    pub(crate) fn mark_garbage(&mut self, c: CRef) {
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
    pub fn add_clause(&mut self, dimacs: &[i32]) {
        let mut lits: Vec<Lit> = Vec::with_capacity(dimacs.len());
        for &d in dimacs {
            let e = Lit::from_dimacs(d);
            self.prepare_external(e.vidx());
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
        self.add_original_clause(&lits);
    }

    /// Add an original (irredundant) clause.  Must be called at level 0.
    pub(crate) fn add_original_clause(&mut self, lits: &[Lit]) {
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
        if simplified.len() != lits.len()
            && let Some(p) = self.proof.as_mut()
        {
            p.add(&simplified);
            p.delete(lits);
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

    /// Push a clause with witness literal `witness` (which must be in the
    /// clause) onto the extension stack.
    pub(crate) fn push_extension(&mut self, witness: Lit, lits: &[Lit]) {
        self.extension.push(self.external(witness).0 | WITNESS);
        for &l in lits {
            if l != witness {
                self.extension.push(self.external(l).0);
            }
        }
    }

    pub fn solve(&mut self) -> SolveResult {
        if self.level > 0 {
            self.backtrack_without_updating_phases(0);
        }
        self.start_assumptions();
        let res = self.search();
        if res == SolveResult::Sat && self.opts.incremental {
            self.last_model = self.model();
        }
        if res != SolveResult::Unsat || self.inconsistent {
            self.failed_assumptions.clear();
        }
        self.end_assumptions();
        self.flush_pending_units();
        if let Some(p) = self.proof.as_mut() {
            p.flush();
        }
        res
    }

    pub(crate) fn terminated(&self) -> bool {
        self.terminate
            .as_ref()
            .is_some_and(|t| t.load(Ordering::Relaxed))
            || self.terminate_callback()
    }

    /// Stop the search (with `SolveResult::Unknown`) when `flag` is set.
    pub fn set_terminate_flag(&mut self, flag: Arc<AtomicBool>) {
        self.terminate = Some(flag);
    }

    pub fn set_conflict_limit(&mut self, conflicts: Option<u64>) {
        self.limits.conflicts = conflicts;
    }

    pub fn set_decision_limit(&mut self, decisions: Option<u64>) {
        self.limits.decisions = decisions;
    }

    pub fn stats(&self) -> &Stats {
        &self.stats
    }

    /// Number of variables (external, including fresh ones introduced by
    /// the solver).
    pub fn num_vars(&self) -> usize {
        self.evars
    }

    /// Seconds since the solver was created.
    pub fn seconds(&self) -> f64 {
        self.start_time.elapsed().as_secs_f64()
    }

    pub(crate) fn verbose(&self, level: u32) -> bool {
        !self.opts.quiet && self.opts.verbose >= level
    }
}
