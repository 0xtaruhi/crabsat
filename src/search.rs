//! Main CDCL search loop with Kissat's mode switching, restarts,
//! rephasing and decisions (`search.c`, `mode.c`, `restart.c`,
//! `rephase.c`, `decide.c`).

use crate::queue::DISCONNECT;
use crate::solver::{ELIMINATED, Solver};
use crate::stats::{logn, nlogpown};
use crate::types::{Lit, SolveResult, Var};

impl Solver {
    pub(crate) fn search(&mut self) -> SolveResult {
        if self.inconsistent {
            return SolveResult::Unsat;
        }
        if self.propagate().is_some() {
            self.mark_inconsistent();
            return SolveResult::Unsat;
        }
        if let Some(res) = self.presolve() {
            return res;
        }
        if self.verbose(4) {
            let pos = self.phases.saved.iter().filter(|&&p| p > 0).count();
            let qlast = self.queue.last;
            let hmax = if self.heap.is_empty() {
                u32::MAX
            } else {
                self.heap.max()
            };
            println!(
                "c [debug] saved positive {pos} of {} queue last {qlast} search {} heap max {hmax} trail {}",
                self.vars,
                self.queue.search_idx,
                self.trail.len()
            );
        }
        self.start_search();
        let res = loop {
            if self.inconsistent {
                break SolveResult::Unsat;
            }
            if let Some(conflict) = self.propagate() {
                if !self.analyze(conflict) {
                    break SolveResult::Unsat;
                }
                // Checked after every analysis so that a chain of conflicts
                // cannot run past the limit.
                if self.conflict_limit_reached() {
                    break SolveResult::Unknown;
                }
            } else if self.iterating {
                self.iterating = false;
                self.report('i');
            } else if self.unassigned == 0 {
                // Remaining assumptions are already assigned (true or false).
                if self.level as usize >= self.incremental.assumptions.len() {
                    break SolveResult::Sat;
                } else if !self.decide() {
                    break SolveResult::Unsat;
                }
            } else if self.terminated() || self.limit_hit() {
                break SolveResult::Unknown;
            } else if self.level == 0 && self.sharing.pool.is_some() && !self.share_units() {
                break SolveResult::Unsat;
            } else if self.reducing() {
                self.reduce();
                self.last_reduce_conflicts = self.stats.conflicts;
            } else if self.switching_search_mode() {
                self.switch_search_mode();
            } else if self.restarting() {
                self.restart();
            } else if self.reordering() {
                self.reorder();
            } else if self.rephasing() {
                if !self.rephase() {
                    break SolveResult::Unsat;
                }
            } else if self.probing_due() {
                if !self.probe() {
                    break SolveResult::Unsat;
                }
            } else if self.eliminating() {
                if !self.eliminate() {
                    break SolveResult::Unsat;
                }
            } else if !self.decide() {
                // A falsified assumption.
                break SolveResult::Unsat;
            }
        };
        self.account_mode_time();
        self.report(match res {
            SolveResult::Sat => '1',
            SolveResult::Unsat => '0',
            SolveResult::Unknown => '?',
        });
        res
    }

    /// Initial decision order by first occurrence of variables in the
    /// input (Kissat's "tumbled" external indices): variables seen first
    /// are decided last in focused mode and first in stable mode.
    fn apply_initial_order(&mut self) {
        if !self.opts.tumble || self.stats.conflicts > 0 {
            return;
        }
        let mut order: Vec<Var> = Vec::with_capacity(self.vars);
        let mut seen = self.seen.clone();
        seen.resize(self.vars, false);
        for v in 0..self.vars as Var {
            if !seen[v as usize] {
                order.push(v);
            }
        }
        order.extend_from_slice(&self.first_seen);
        self.queue.rebuild(&order);
        self.heap.clear();
        for &v in &order {
            if !self.flags[v as usize].has(ELIMINATED) {
                self.heap.push(v);
            }
        }
    }

    /// Initial order, lucky phases and preprocessing (once).  Returns a
    /// result if the formula was already solved.
    pub(crate) fn presolve(&mut self) -> Option<SolveResult> {
        if self.presolved {
            return None;
        }
        self.presolved = true;
        if self.inconsistent {
            return Some(SolveResult::Unsat);
        }
        if self.propagate().is_some() {
            self.mark_inconsistent();
            return Some(SolveResult::Unsat);
        }
        self.apply_initial_order();
        // Kissat tries lucky assignments before and after preprocessing
        // (not with assumptions, which lucky assignments ignore).
        let lucky = self.incremental.assumptions.is_empty();
        if lucky && self.opts.luckyearly && self.lucky_early() {
            return Some(SolveResult::Sat);
        }
        if !self.preprocess() {
            return Some(SolveResult::Unsat);
        }
        if lucky && self.opts.luckylate && self.lucky() {
            return Some(SolveResult::Sat);
        }
        None
    }

    fn limit_hit(&self) -> bool {
        self.conflict_limit_reached()
            || self
                .limits
                .decisions_end
                .is_some_and(|l| self.stats.decisions >= l)
    }

    fn start_search(&mut self) {
        self.stable = self.opts.stable == 2;
        self.mode_start = self.seconds();
        let (fast, slow) = (self.opts.emafast as f64, self.opts.emaslow as f64);
        self.averages[self.stable as usize].init(fast, slow);
        if self.stable {
            self.init_reluctant();
            self.update_scores();
        }
        for stable in 0..2 {
            if self.tier1[stable] == 0 {
                self.tier1[stable] = self.opts.tier1;
                self.tier2[stable] = self.opts.tier2.max(self.opts.tier1);
            }
        }
        if self.limits.glue_interval == 0 {
            self.limits.glue_interval = 2;
        }
        let conflicts = self.stats.conflicts;
        self.limits.reduce_conflicts = conflicts + self.opts.reduceinit;
        self.limits.rephase_conflicts = conflicts + self.opts.rephaseinit;
        if !self.stable {
            self.update_focused_restart_limit();
        }
        self.limits.eliminate_conflicts = conflicts + self.scale_delta(self.opts.eliminateinit);
        self.limits.probe_conflicts = conflicts + self.scale_delta(self.opts.probeinit);
        self.limits.reorder_conflicts = conflicts + self.opts.reorderinit;
        self.limits.randec_conflicts = conflicts + self.opts.randecinit;
        self.init_mode_limit();
        self.report('*');
    }

    // ------------------------------------------------------------------
    // Decisions.

    fn last_enqueued_unassigned_variable(&mut self) -> Var {
        let mut res = self.queue.search_idx;
        debug_assert!(res != DISCONNECT);
        if self.values[Lit::new(res, false).idx()] != 0 {
            loop {
                res = self.queue.links[res as usize].prev;
                if self.values[Lit::new(res, false).idx()] == 0 {
                    break;
                }
            }
            self.queue.update_search(res);
        }
        res
    }

    fn largest_score_unassigned_variable(&mut self) -> Var {
        let mut res = self.heap.max();
        while self.values[Lit::new(res, false).idx()] != 0
            || self.flags[res as usize].has(ELIMINATED)
        {
            self.heap.pop_max();
            res = self.heap.max();
        }
        res
    }

    pub(crate) fn next_decision_variable(&mut self) -> Var {
        if let Some(v) = self.next_random_decision() {
            return v;
        }
        if self.stable {
            self.largest_score_unassigned_variable()
        } else {
            self.last_enqueued_unassigned_variable()
        }
    }

    /// Assign all variables by decisions with saved/target phases and
    /// propagation which ignores conflicts, which makes the saved phases
    /// more consistent before local search (Kissat `warmup.c`).
    pub(crate) fn warmup(&mut self) {
        debug_assert_eq!(self.level, 0);
        self.warming = true;
        while self.unassigned > 0 && !self.terminated() {
            let v = self.next_decision_variable();
            let phase = self.decide_phase(v);
            self.assign_decision(Lit::new(v, phase < 0));
            while self.propagate().is_some() {}
        }
        self.backtrack_without_updating_phases(0);
        self.warming = false;
    }

    pub(crate) fn decide_phase(&self, v: Var) -> i8 {
        if self.incremental.any_forced {
            let forced = self.forced_phase(v);
            if forced != 0 {
                return forced;
            }
        }
        let initial: i8 = if self.opts.phase { 1 } else { -1 };
        let use_target = match self.opts.target {
            0 => false,
            1 => self.stable,
            _ => true,
        };
        let mut res: i8 = 0;
        if !self.stable {
            match (self.stats.switched >> 1) & 7 {
                1 => res = initial,
                3 => res = -initial,
                _ => {}
            }
        }
        if res == 0 && use_target {
            res = self.phases.target[v as usize];
        }
        if res == 0 && self.opts.phasesaving {
            res = self.phases.saved[v as usize];
        }
        if res == 0 {
            res = initial;
        }
        res
    }

    /// Returns false if an assumption is falsified.
    fn decide(&mut self) -> bool {
        if let Some(ok) = self.decide_assumption() {
            return ok;
        }
        self.stats.decisions += 1;
        let v = self.next_decision_variable();
        let phase = self.decide_phase(v);
        self.assign_decision(Lit::new(v, phase < 0));
        true
    }

    pub(crate) fn update_scores(&mut self) {
        for v in 0..self.vars as Var {
            if !self.flags[v as usize].has(ELIMINATED) && !self.heap.contains(v) {
                self.heap.push(v);
            }
        }
    }

    // ------------------------------------------------------------------
    // Restarts.

    fn init_reluctant(&mut self) {
        if self.opts.reluctant {
            self.reluctant
                .enable(self.opts.reluctantint, self.opts.reluctantlim);
        } else {
            self.reluctant.disable();
        }
    }

    fn restarting(&mut self) -> bool {
        if !self.opts.restart || self.level == 0 {
            return false;
        }
        if self.stats.conflicts < self.limits.restart_conflicts {
            return false;
        }
        if self.stable {
            return self.reluctant.triggered();
        }
        let avg = &self.averages[0];
        let margin = (100.0 + self.opts.restartmargin as f64) / 100.0;
        margin * avg.slow_glue.value <= avg.fast_glue.value
    }

    fn update_focused_restart_limit(&mut self) {
        let restarts = self.stats.restarts;
        let mut delta = self.opts.restartint as f64;
        if restarts > 0 {
            delta += logn(restarts) - 1.0;
        }
        self.limits.restart_conflicts = self.stats.conflicts + delta as u64;
    }

    /// Number of levels which can be kept because their decisions are
    /// still preferred over the next decision.
    fn reuse_trail(&mut self) -> u32 {
        if !self.opts.restartreusetrail {
            return 0;
        }
        let next = self.next_decision_variable();
        // Assumption levels are always kept.
        let mut res = (self.incremental.assumptions.len() as u32).min(self.level);
        if self.stable {
            let limit = self.heap.score[next as usize];
            while res < self.level {
                let d = self.frames[res as usize + 1].decision;
                if self.heap.score[d.vidx()] <= limit {
                    break;
                }
                res += 1;
            }
        } else {
            let limit = self.queue.links[next as usize].stamp;
            while res < self.level {
                let d = self.frames[res as usize + 1].decision;
                if self.queue.links[d.vidx()].stamp <= limit {
                    break;
                }
                res += 1;
            }
        }
        self.stats.restarts_reused_levels += res as u64;
        res
    }

    fn restart(&mut self) {
        self.stats.restarts += 1;
        if self.sharing.pool.is_some() {
            if !self.share_clauses() {
                return;
            }
            if self.level == 0 {
                // Clauses were imported at the root level.
                if !self.stable {
                    self.update_focused_restart_limit();
                }
                return;
            }
        }
        let level = self.reuse_trail();
        self.backtrack_in_consistent_state(level);
        if !self.stable {
            self.update_focused_restart_limit();
        }
        if self.verbose(3) {
            self.report('R');
        }
    }

    // ------------------------------------------------------------------
    // Mode switching.

    fn init_mode_limit(&mut self) {
        if self.opts.stable == 1 {
            self.limits.mode_conflicts = self.stats.conflicts + self.opts.modeinit;
            self.limits.mode_ticks = 0;
            self.limits.mode_count = 0;
            self.mode_ticks = self.stats.search_ticks;
        }
    }

    fn switching_search_mode(&self) -> bool {
        if self.opts.stable != 1 {
            return false;
        }
        if self.limits.mode_count & 1 != 0 {
            self.stats.search_ticks >= self.limits.mode_ticks
        } else {
            self.stats.conflicts >= self.limits.mode_conflicts
        }
    }

    fn update_mode_limit(&mut self, delta_ticks: u64) {
        let (fast, slow) = (self.opts.emafast as f64, self.opts.emaslow as f64);
        self.averages[self.stable as usize].init(fast, slow);
        if self.limits.mode_count & 1 != 0 {
            self.limits.mode_ticks = self.stats.search_ticks + delta_ticks;
        } else {
            let count = self.stats.switched.div_ceil(2);
            let scaled = self.opts.modeint as f64 * nlogpown(count, 4);
            self.limits.mode_conflicts = self.stats.conflicts + scaled as u64;
        }
        self.mode_ticks = self.stats.search_ticks;
    }

    fn account_mode_time(&mut self) {
        let now = self.seconds();
        let delta = now - self.mode_start;
        if self.stable {
            self.stats.time_stable += delta;
        } else {
            self.stats.time_focused += delta;
        }
        self.mode_start = now;
    }

    fn switch_search_mode(&mut self) {
        self.account_mode_time();
        self.stats.switched += 1;
        self.limits.mode_count += 1;
        let delta_ticks = self.stats.search_ticks - self.mode_ticks;
        if self.stable {
            self.report(']');
            self.stable = false;
            self.update_mode_limit(delta_ticks);
            self.queue.reset_search();
            self.update_focused_restart_limit();
            self.report('{');
        } else {
            self.report('}');
            self.stable = true;
            self.update_mode_limit(delta_ticks);
            self.init_reluctant();
            self.update_scores();
            self.report('[');
        }
        self.averages[self.stable as usize].saved_decisions = self.stats.decisions;
        self.start_random_sequence();
    }

    // ------------------------------------------------------------------
    // Rephasing.

    fn rephasing(&self) -> bool {
        self.opts.rephase && self.stable && self.stats.conflicts > self.limits.rephase_conflicts
    }

    fn rephase(&mut self) -> bool {
        if !self.backtrack_propagate_root() {
            return false;
        }
        self.stats.rephased += 1;
        // Kissat: best, walk, inverted, best, walk, original.
        let initial: i8 = if self.opts.phase { 1 } else { -1 };
        let select = (self.stats.rephased - 1) % 6;
        let kind = match select {
            1 | 4 if self.opts.walkeffort > 0 => {
                self.walk();
                'W'
            }
            0 | 1 | 3 | 4 => {
                for (s, &b) in self.phases.saved.iter_mut().zip(&self.phases.best) {
                    if b != 0 {
                        *s = b;
                    }
                }
                'B'
            }
            2 => {
                self.phases.saved.fill(-initial);
                'I'
            }
            _ => {
                self.phases.saved.fill(initial);
                'O'
            }
        };
        self.phases.target.copy_from_slice(&self.phases.saved);
        let delta = self.opts.rephaseint as f64 * nlogpown(self.stats.rephased, 3);
        self.limits.rephase_conflicts = self.stats.conflicts + delta as u64;
        self.target_assigned = 0;
        if kind == 'B' {
            self.best_assigned = 0;
        }
        self.report(kind);
        true
    }

    // ------------------------------------------------------------------

    pub(crate) fn report(&self, kind: char) {
        if !self.verbose(1) {
            return;
        }
        let s = &self.stats;
        let mb = (self.arena.len() * 4) as f64 / (1 << 20) as f64;
        println!(
            "c {} {:8.2}s {:>10} conflicts {:>8} red {:>8} irr {:>7} bin \
             {:>6} glue {:>6.1}/{:<6.1} {:6.1}MB {:>7} assigned",
            kind,
            self.seconds(),
            s.conflicts,
            s.clauses_redundant,
            s.clauses_irredundant,
            s.clauses_binary,
            self.tier2_limit(),
            self.averages[self.stable as usize].fast_glue.value,
            self.averages[self.stable as usize].slow_glue.value,
            mb,
            self.assigned_count(),
        );
    }
}
