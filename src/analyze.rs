//! Conflict analysis (Kissat `analyze.c`, `deduce.c`, `minimize.c`,
//! `shrink.c`, `learn.c`, `bump.c`).

use crate::arena::{CRef, INVALID_REF, MAX_USED};
use crate::solver::{
    Conflict, Solver, ANALYZED, BINARY, DECISION_REASON, INVALID_LEVEL, POISONED, REMOVABLE,
    SHRINKABLE,
};
use crate::stats::MAX_GLUE_USED;
use crate::types::{Lit, Var};

const MAX_SCORE: f64 = 1e150;

impl Solver {
    /// Analyze a conflict, learn a clause and backtrack.  Returns `false` if
    /// the formula was found to be unsatisfiable.
    pub fn analyze(&mut self, mut conflict: Conflict) -> bool {
        if self.inconsistent {
            return false;
        }
        if self.randec > 0 {
            self.randec -= 1;
        }
        self.update_decision_rate_average();
        loop {
            let (handled, conflict_level) = self.one_literal_on_conflict_level(conflict);
            let mut again = None;
            if handled {
                // Missed lower implication (chronological backtracking).
            } else if conflict_level == 0 {
                self.mark_inconsistent();
                return false;
            } else if let Some(strengthened) = self.deduce_first_uip_clause(conflict) {
                // On-the-fly strengthening produced a new conflict.
                self.reset_analysis_but_not_analyzed_literals();
                self.stats.conflicts += 1;
                again = Some(strengthened);
            } else {
                if self.opts.minimize {
                    self.sort_deduced_clause();
                    self.minimize_clause();
                    if self.opts.shrink > 0 {
                        self.shrink_clause();
                    }
                }
                self.analyze_reason_side_literals();
                self.learn_clause();
                self.reset_analysis_but_not_analyzed_literals();
                if self.stats.conflicts > self.limits.glue_conflicts {
                    self.update_tier_limits();
                }
            }
            if !self.analyzed.is_empty() {
                if self.opts.bump {
                    self.bump_analyzed();
                }
                self.reset_analyzed();
            }
            match again {
                Some(c) => conflict = c,
                None => break,
            }
        }
        !self.inconsistent
    }

    fn update_decision_rate_average(&mut self) {
        let stable = self.stable as usize;
        let current = self.stats.decisions;
        let avg = &mut self.averages[stable];
        let delta = current - avg.saved_decisions;
        avg.saved_decisions = current;
        avg.decision_rate.update(delta as f64);
    }

    fn conflict_lits(&self, conflict: Conflict) -> ConflictLits {
        match conflict {
            Conflict::Binary(a, b) => ConflictLits::Binary([a, b]),
            Conflict::Large(c) => ConflictLits::Large(c),
        }
    }

    /// Kissat's `one_literal_on_conflict_level`: handles conflicts below the
    /// current decision level and conflicts with a single literal on the
    /// conflict level (both possible due to chronological backtracking).
    fn one_literal_on_conflict_level(&mut self, conflict: Conflict) -> (bool, u32) {
        let cl = self.conflict_lits(conflict);
        let lits: &[Lit] = match &cl {
            ConflictLits::Binary(l) => l,
            ConflictLits::Large(c) => self.arena.lits(*c),
        };
        let mut jump_level = INVALID_LEVEL;
        let mut conflict_level = INVALID_LEVEL;
        let mut on_conflict_level = 0u32;
        let mut forced = Lit::INVALID;
        for &lit in lits {
            let lit_level = self.assigned[lit.vidx()].level;
            if conflict_level == INVALID_LEVEL || conflict_level < lit_level {
                on_conflict_level = 1;
                jump_level = conflict_level;
                conflict_level = lit_level;
                forced = lit;
            } else {
                if jump_level == INVALID_LEVEL || jump_level < lit_level {
                    jump_level = lit_level;
                }
                if conflict_level == lit_level {
                    on_conflict_level += 1;
                }
            }
            if on_conflict_level > 1 && conflict_level == self.level {
                break;
            }
        }
        if conflict_level == 0 {
            return (false, 0);
        }
        if conflict_level < self.level {
            self.backtrack_after_conflict(conflict_level);
        }
        if let ConflictLits::Large(c) = cl {
            // Move the two highest-level literals to the watched positions.
            let size = self.arena.size(c);
            for i in 0..2 {
                let lit = self.arena.lits(c)[i];
                let mut highest_pos = i;
                let mut highest_level = self.level_of(lit);
                for j in i + 1..size {
                    let other = self.arena.lits(c)[j];
                    let level = self.level_of(other);
                    if highest_level >= level {
                        continue;
                    }
                    highest_pos = j;
                    highest_level = level;
                    if highest_level == conflict_level {
                        break;
                    }
                }
                if highest_pos == i {
                    continue;
                }
                if highest_pos > 1 {
                    crate::watch::remove_large(&mut self.watches[lit.idx()], c);
                }
                let lits = self.arena.lits_mut(c);
                lits.swap(i, highest_pos);
                let (new, blocking) = (lits[i], lits[1 - i]);
                if highest_pos > 1 {
                    crate::watch::push_large(&mut self.watches[new.idx()], blocking, c);
                }
            }
        }
        if on_conflict_level > 1 {
            return (false, conflict_level);
        }
        let new_level = self.determine_new_level(jump_level);
        self.backtrack_after_conflict(new_level);
        match cl {
            ConflictLits::Binary([a, b]) => {
                let other = if a == forced { b } else { a };
                self.assign_binary(forced, other);
            }
            ConflictLits::Large(c) => self.assign_reference(forced, c),
        }
        (true, conflict_level)
    }

    #[inline]
    fn push_analyzed(&mut self, v: Var) {
        let a = &mut self.assigned[v as usize];
        debug_assert!(!a.has(ANALYZED));
        a.flags |= ANALYZED;
        self.analyzed.push(v);
    }

    /// Returns true if the literal is on the current decision level.
    #[inline]
    fn analyze_literal(&mut self, lit: Lit) -> bool {
        let a = self.assigned[lit.vidx()];
        if a.level == 0 {
            return false;
        }
        self.antecedent_size += 1;
        if a.has(ANALYZED) {
            return false;
        }
        self.push_analyzed(lit.var());
        self.resolvent_size += 1;
        if a.level == self.level {
            return true;
        }
        self.clause.push(lit);
        let f = &mut self.frames[a.level as usize];
        f.used += 1;
        if f.used == 1 {
            self.levels.push(a.level);
        }
        false
    }

    fn recompute_glue(&mut self, c: CRef, limit: u32) -> u32 {
        let mut res = 0;
        for i in 0..self.arena.size(c) {
            let lit = self.arena.lits(c)[i];
            let level = self.level_of(lit);
            let f = &mut self.frames[level as usize];
            if f.promote {
                continue;
            }
            res += 1;
            if res == limit {
                break;
            }
            f.promote = true;
            self.promote_levels.push(level);
        }
        for &level in &self.promote_levels {
            self.frames[level as usize].promote = false;
        }
        self.promote_levels.clear();
        res
    }

    fn mark_clause_as_used(&mut self, c: CRef) {
        if !self.arena.redundant(c) {
            return;
        }
        self.arena.set_used(c, MAX_USED);
        let old_glue = self.arena.glue(c);
        let new_glue = self.recompute_glue(c, old_glue);
        if new_glue < old_glue && self.opts.promote {
            self.arena.set_glue(c, new_glue);
            self.stats.promoted += 1;
        }
        let glue = (self.arena.glue(c) as usize).min(MAX_GLUE_USED);
        self.stats.used[self.stable as usize][glue] += 1;
    }

    /// Derive the first UIP clause into `self.clause`.  Returns a new
    /// conflict if a reason clause was strengthened on-the-fly instead.
    fn deduce_first_uip_clause(&mut self, conflict: Conflict) -> Option<Conflict> {
        debug_assert!(self.clause.is_empty());
        self.clause.push(Lit::INVALID);
        self.antecedent_size = 0;
        self.resolvent_size = 0;
        let mut unresolved = 0u32;
        match conflict {
            Conflict::Binary(a, b) => {
                unresolved += self.analyze_literal(a) as u32;
                unresolved += self.analyze_literal(b) as u32;
            }
            Conflict::Large(c) => {
                self.mark_clause_as_used(c);
                for i in 0..self.arena.size(c) {
                    let lit = self.arena.lits(c)[i];
                    unresolved += self.analyze_literal(lit) as u32;
                }
            }
        }
        let conflict_size = self.antecedent_size;
        let mut resolved = 0;
        let mut t = self.trail.len();
        let uip;
        loop {
            let (lit, a) = loop {
                t -= 1;
                let lit = self.trail[t];
                let a = self.assigned[lit.vidx()];
                if a.has(ANALYZED) && a.level == self.level {
                    break (lit, a);
                }
            };
            if unresolved == 1 {
                uip = lit;
                break;
            }
            self.antecedent_size = 1;
            resolved += 1;
            if a.has(BINARY) {
                unresolved += self.analyze_literal(Lit(a.reason)) as u32;
            } else {
                let c = a.reason;
                debug_assert!(c != DECISION_REASON);
                for i in 0..self.arena.size(c) {
                    let other = self.arena.lits(c)[i];
                    if other != lit {
                        unresolved += self.analyze_literal(other) as u32;
                    }
                }
                self.mark_clause_as_used(c);
            }
            unresolved -= 1;
            self.resolvent_size -= 1;
            if self.opts.otfs
                && self.antecedent_size > 2
                && self.resolvent_size < self.antecedent_size
            {
                // The resolvent is the reason without `lit`.
                let reason = a.reason;
                let strengthened = self.on_the_fly_strengthen(reason, lit);
                if resolved == 1 && self.resolvent_size < conflict_size {
                    if let Conflict::Large(d) = conflict {
                        if !self.arena.garbage(d) && d != reason {
                            self.on_the_fly_subsume(strengthened, d);
                        }
                    }
                }
                return Some(strengthened);
            }
        }
        self.clause[0] = !uip;
        self.stats.literals_deduced += self.clause.len() as u64;
        None
    }

    /// The strengthened clause `c` subsumes the conflict `d`, which is
    /// deleted.  If `d` was irredundant, `c` must become irredundant too
    /// (Kissat `kissat_on_the_fly_subsume`).
    fn on_the_fly_subsume(&mut self, c: Conflict, d: CRef) {
        self.stats.otfs_subsumed += 1;
        let d_redundant = self.arena.redundant(d);
        let d_glue = self.arena.glue(d);
        self.mark_garbage(d);
        match c {
            Conflict::Large(c) => {
                if !self.arena.redundant(c) {
                    return;
                }
                if d_redundant {
                    if self.arena.glue(c) > d_glue {
                        self.arena.set_glue(c, d_glue);
                    }
                    return;
                }
                self.arena.set_redundant(c, false);
                self.stats.clauses_redundant -= 1;
                self.stats.clauses_irredundant += 1;
                let lits = self.arena.lits(c).to_vec();
                for l in lits {
                    self.mark_added_lit(l);
                }
            }
            // Binary clauses are always irredundant.
            Conflict::Binary(..) => {}
        }
    }

    /// Remove the (true) literal `lit` and root-level literals from its
    /// reason `c`; the result is a falsified clause.
    fn on_the_fly_strengthen(&mut self, c: CRef, lit: Lit) -> Conflict {
        self.stats.otfs_strengthened += 1;
        let old: Vec<Lit> = self.arena.lits(c).to_vec();
        let mut lits: Vec<Lit> =
            old.iter().copied().filter(|&l| l != lit && self.level_of(l) > 0).collect();
        if !self.arena.redundant(c) {
            self.mark_removed_var(lit.vidx());
        }
        self.unwatch_clause(c);
        if let Some(p) = self.proof.as_mut() {
            p.add(&lits);
        }
        if lits.len() == 2 {
            self.mark_garbage(c);
            self.new_binary(lits[0], lits[1]);
            return Conflict::Binary(lits[0], lits[1]);
        }
        if let Some(p) = self.proof.as_mut() {
            p.delete(&old);
        }
        // Watch the two literals with the highest levels.
        for i in 0..2 {
            let mut best = i;
            for j in i + 1..lits.len() {
                if self.level_of(lits[j]) > self.level_of(lits[best]) {
                    best = j;
                }
            }
            lits.swap(i, best);
        }
        let size = lits.len();
        self.arena.lits_mut(c)[..size].copy_from_slice(&lits);
        self.arena.shrink(c, size);
        self.arena.set_searched(c, 2);
        if self.arena.redundant(c) && self.arena.glue(c) as usize >= size {
            self.arena.set_glue(c, size as u32 - 1);
        }
        self.watch_clause(c);
        Conflict::Large(c)
    }

    /// Sort literals after the UIP by decreasing level (needed by shrinking).
    fn sort_deduced_clause(&mut self) {
        let assigned = &self.assigned;
        self.clause[1..].sort_unstable_by_key(|l| std::cmp::Reverse(assigned[l.vidx()].level));
    }

    #[inline]
    fn push_removable(&mut self, v: Var) {
        self.assigned[v as usize].flags |= REMOVABLE;
        self.removable.push(v);
    }

    #[inline]
    fn push_poisoned(&mut self, v: Var) {
        self.assigned[v as usize].flags |= POISONED;
        self.poisoned.push(v);
    }

    /// 1 = removable, -1 = not removable, 0 = needs recursion.
    #[inline]
    fn minimized_index(&self, minimizing: bool, v: Var, depth: u32) -> i32 {
        let a = &self.assigned[v as usize];
        if a.level == 0 {
            return 1;
        }
        if a.has(REMOVABLE) && depth > 0 {
            return 1;
        }
        if a.reason == DECISION_REASON && !a.has(BINARY) {
            return -1;
        }
        if a.has(POISONED) {
            return -1;
        }
        if (minimizing || depth == 0) && self.frames[a.level as usize].used <= 1 {
            return -1;
        }
        0
    }

    fn minimize_reference(&mut self, minimizing: bool, c: CRef, lit: Lit, depth: u32) -> bool {
        let next_depth = depth.saturating_add(1);
        let not_lit = !lit;
        for i in 0..self.arena.size(c) {
            let other = self.arena.lits(c)[i];
            if other != not_lit && !self.minimize_literal(minimizing, other, next_depth) {
                return false;
            }
        }
        true
    }

    fn minimize_binary(&mut self, minimizing: bool, lit: Lit, depth: u32) -> bool {
        let saved = self.minimize_stack.len();
        let mut next = lit;
        let res;
        loop {
            let v = next.var();
            let tmp = self.minimized_index(minimizing, v, 1);
            if tmp != 0 {
                res = tmp > 0;
                break;
            }
            self.minimize_stack.push(v);
            let a = self.assigned[v as usize];
            if !a.has(BINARY) {
                res = self.minimize_reference(minimizing, a.reason, next, depth.saturating_add(1));
                break;
            }
            next = Lit(a.reason);
        }
        for i in saved..self.minimize_stack.len() {
            let v = self.minimize_stack[i];
            if res {
                self.push_removable(v);
            } else {
                self.push_poisoned(v);
            }
        }
        self.minimize_stack.truncate(saved);
        res
    }

    fn minimize_literal(&mut self, minimizing: bool, lit: Lit, depth: u32) -> bool {
        if depth >= self.opts.minimizedepth {
            return false;
        }
        let v = lit.var();
        let tmp = self.minimized_index(minimizing, v, depth);
        if tmp > 0 {
            return true;
        }
        if tmp < 0 {
            return false;
        }
        let a = self.assigned[v as usize];
        let res = if a.has(BINARY) {
            self.minimize_binary(minimizing, Lit(a.reason), depth)
        } else {
            self.minimize_reference(minimizing, a.reason, lit, depth)
        };
        if depth == 0 {
            return res;
        }
        if !res {
            self.push_poisoned(v);
        } else if !self.assigned[v as usize].has(REMOVABLE) {
            self.push_removable(v);
        }
        res
    }

    fn reset_poisoned(&mut self) {
        for &v in &self.poisoned {
            self.assigned[v as usize].flags &= !POISONED;
        }
        self.poisoned.clear();
    }

    fn minimize_clause(&mut self) {
        for i in 0..self.clause.len() {
            let v = self.clause[i].var();
            self.push_removable(v);
        }
        if self.opts.shrink > 2 {
            return;
        }
        let mut minimized = 0;
        for i in (1..self.clause.len()).rev() {
            let lit = self.clause[i];
            if self.minimize_literal(true, lit, 0) {
                self.clause[i] = Lit::INVALID;
                minimized += 1;
            }
        }
        self.clause.retain(|&l| l != Lit::INVALID);
        self.stats.literals_minimized += minimized;
        self.reset_poisoned();
    }

    // ------------------------------------------------------------------
    // Shrinking (Kissat `shrink.c`).

    fn reset_shrinkable(&mut self) {
        while let Some(v) = self.shrinkable.pop() {
            self.assigned[v as usize].flags &= !SHRINKABLE;
        }
    }

    fn mark_shrinkable_as_removable(&mut self) {
        while let Some(v) = self.shrinkable.pop() {
            let a = &mut self.assigned[v as usize];
            a.flags &= !SHRINKABLE;
            if !a.has(REMOVABLE) {
                self.push_removable(v);
            }
        }
    }

    /// 1 = new literal on `level`, 0 = ignore, -1 = fail.
    #[inline]
    fn shrink_literal(&mut self, level: u32, lit: Lit) -> i32 {
        let v = lit.var();
        let a = self.assigned[v as usize];
        if a.level == 0 || a.has(SHRINKABLE) {
            return 0;
        }
        if a.level < level {
            if a.has(REMOVABLE) {
                return 0;
            }
            if self.opts.shrink > 2 && self.minimize_literal(false, lit, 1) {
                return 0;
            }
            return -1;
        }
        self.assigned[v as usize].flags |= SHRINKABLE;
        self.shrinkable.push(v);
        1
    }

    fn shrink_along_reason(&mut self, level: u32, uip: Lit, failed: &mut bool) -> u32 {
        let a = self.assigned[uip.vidx()];
        if a.has(BINARY) {
            return (self.shrink_literal(level, Lit(a.reason)) > 0) as u32;
        }
        if self.opts.shrink < 2 {
            *failed = true;
            return 0;
        }
        let c = a.reason;
        let mut open = 0;
        for i in 0..self.arena.size(c) {
            let other = self.arena.lits(c)[i];
            if other == uip {
                continue;
            }
            let tmp = self.shrink_literal(level, other);
            if tmp < 0 {
                *failed = true;
                break;
            }
            if tmp > 0 {
                open += 1;
            }
        }
        open
    }

    fn shrink_block(&mut self, begin: usize, end: usize, level: u32, max_trail: usize) -> u64 {
        let mut open = (end - begin) as u32;
        for i in begin..end {
            let lit = self.clause[i];
            self.shrink_literal(level, lit);
        }
        let mut t = max_trail;
        let mut failed = false;
        let mut uip;
        loop {
            loop {
                uip = self.trail[t];
                if self.assigned[uip.vidx()].has(SHRINKABLE) {
                    break;
                }
                t -= 1;
            }
            if open == 1 {
                break;
            }
            t = t.wrapping_sub(1);
            open += self.shrink_along_reason(level, uip, &mut failed);
            open -= 1;
            if failed {
                break;
            }
        }
        if failed {
            self.reset_shrinkable();
            return 0;
        }
        // Replace the whole block by the negation of its UIP.
        let mut shrunken = 0;
        for i in begin..end {
            if self.clause[i] != Lit::INVALID {
                self.clause[i] = Lit::INVALID;
                shrunken += 1;
            }
        }
        self.clause[begin] = !uip;
        shrunken -= 1;
        let uv = uip.var();
        if !self.assigned[uv as usize].has(ANALYZED) {
            self.push_analyzed(uv);
        }
        self.mark_shrinkable_as_removable();
        shrunken
    }

    fn minimize_block(&mut self, begin: usize, end: usize) -> u64 {
        let mut minimized = 0;
        for i in begin..end {
            let lit = self.clause[i];
            if self.minimize_literal(false, lit, 0) {
                self.clause[i] = Lit::INVALID;
                minimized += 1;
            }
        }
        minimized
    }

    fn shrink_clause(&mut self) {
        let mut end_block = self.clause.len();
        let mut total_shrunken = 0;
        let mut total_minimized = 0;
        while end_block > 0 {
            // Find the block of literals on the same (lowest remaining) level.
            let mut level = INVALID_LEVEL;
            let mut max_trail = 0usize;
            let mut begin_block = end_block;
            while begin_block > 0 {
                let lit = self.clause[begin_block - 1];
                let a = self.assigned[lit.vidx()];
                if level == INVALID_LEVEL {
                    level = a.level;
                } else if a.level > level {
                    break;
                }
                begin_block -= 1;
                max_trail = max_trail.max(a.trail as usize);
            }
            let open = end_block - begin_block;
            if open >= 2 {
                let shrunken = self.shrink_block(begin_block, end_block, level, max_trail);
                if shrunken > 0 {
                    total_shrunken += shrunken;
                } else {
                    total_minimized += self.minimize_block(begin_block, end_block);
                }
            }
            end_block = begin_block;
        }
        self.clause.retain(|&l| l != Lit::INVALID);
        self.stats.literals_shrunken += total_shrunken;
        self.stats.literals_minimized += total_minimized;
        self.reset_poisoned();
    }

    // ------------------------------------------------------------------

    fn analyze_reason_side_literals(&mut self) {
        if !self.opts.bump || !self.opts.bumpreasons {
            return;
        }
        if self.delay_bumpreasons.delaying() {
            return;
        }
        let rate = self.averages[self.stable as usize].decision_rate.value;
        if rate >= self.opts.bumpreasonsrate as f64 {
            return;
        }
        let saved = self.analyzed.len();
        let limit = self.opts.bumpreasonslimit as usize * saved;
        'outer: for i in 0..self.clause.len() {
            let lit = self.clause[i];
            let a = self.assigned[lit.vidx()];
            if a.reason == DECISION_REASON && !a.has(BINARY) {
                continue;
            }
            if a.has(BINARY) {
                self.mark_reason_side_literal(Lit(a.reason));
            } else {
                let not_lit = !lit;
                for j in 0..self.arena.size(a.reason) {
                    let other = self.arena.lits(a.reason)[j];
                    if other != not_lit {
                        self.mark_reason_side_literal(other);
                        if self.analyzed.len() > limit {
                            break 'outer;
                        }
                    }
                }
            }
            if self.analyzed.len() > limit {
                break;
            }
        }
        if self.analyzed.len() > limit {
            while self.analyzed.len() > saved {
                let v = self.analyzed.pop().unwrap();
                self.assigned[v as usize].flags &= !ANALYZED;
            }
            self.delay_bumpreasons.bump();
        } else {
            self.delay_bumpreasons.reduce();
        }
    }

    #[inline]
    fn mark_reason_side_literal(&mut self, lit: Lit) {
        let a = self.assigned[lit.vidx()];
        if a.level > 0 && !a.has(ANALYZED) {
            self.push_analyzed(lit.var());
        }
    }

    pub fn determine_new_level(&mut self, jump: u32) -> u32 {
        let back = self.level - 1;
        let delta = back - jump;
        let limit = if self.opts.chrono { self.opts.chronolevels } else { u32::MAX };
        if delta > limit {
            self.stats.chronological += 1;
            back
        } else {
            jump
        }
    }

    fn update_learned(&mut self, glue: u32, size: usize) {
        self.stats.clauses_learned += 1;
        self.stats.literals_learned += size as u64;
        if self.stable {
            self.reluctant.tick();
        }
        let avg = &mut self.averages[self.stable as usize];
        avg.fast_glue.update(glue as f64);
        avg.slow_glue.update(glue as f64);
    }

    fn learn_clause(&mut self) {
        let not_uip = self.clause[0];
        let size = self.clause.len();
        let glue = self.levels.len() as u32;
        if self.shared.is_some() && size >= 2 {
            let lits = std::mem::take(&mut self.clause);
            self.export_clause(&lits, glue);
            self.clause = lits;
        }
        self.update_learned(glue, size);
        let mut learned = INVALID_REF;
        if size == 1 {
            let new_level = self.determine_new_level(0);
            self.backtrack_after_conflict(new_level);
            self.learned_unit(not_uip);
            self.iterating = true;
            self.stats.iterations += 1;
        } else if size == 2 {
            let other = self.clause[1];
            let jump = self.level_of(other);
            let new_level = self.determine_new_level(jump);
            self.backtrack_after_conflict(new_level);
            if let Some(p) = self.proof.as_mut() {
                p.add(&[not_uip, other]);
            }
            self.new_binary(not_uip, other);
            self.assign_binary(not_uip, other);
        } else {
            // Put the literal with the highest level at position 1.
            let back = self.level - 1;
            let mut pos = 1;
            let mut jump_level = self.level_of(self.clause[1]);
            for i in 2..size {
                let level = self.level_of(self.clause[i]);
                if jump_level >= level {
                    continue;
                }
                jump_level = level;
                pos = i;
                if level == back {
                    break;
                }
            }
            self.clause.swap(1, pos);
            let lits = std::mem::take(&mut self.clause);
            if let Some(p) = self.proof.as_mut() {
                p.add(&lits);
            }
            let c = self.new_large(&lits, true, glue);
            self.clause = lits;
            self.arena.set_used(c, MAX_USED);
            let new_level = self.determine_new_level(jump_level);
            self.backtrack_after_conflict(new_level);
            self.assign_reference(not_uip, c);
            learned = c;
        }
        if self.opts.eagersubsume > 0 {
            self.eagerly_subsume_last_learned();
            if learned != INVALID_REF {
                self.last_learned.rotate_right(1);
                self.last_learned[0] = learned;
            }
        }
    }

    /// Is the large clause `c` the reason of one of its watched literals?
    pub fn is_reason(&self, c: CRef) -> bool {
        let lits = self.arena.lits(c);
        lits[..2].iter().any(|&l| {
            let a = &self.assigned[l.vidx()];
            self.value(l) > 0 && a.level > 0 && !a.has(BINARY) && a.reason == c
        })
    }

    fn eagerly_subsume_last_learned(&mut self) {
        for &lit in &self.clause {
            self.marks[lit.idx()] = 1;
        }
        let clause_size = self.clause.len();
        for k in 0..self.last_learned.len() {
            let c = self.last_learned[k];
            if c == INVALID_REF {
                continue;
            }
            if self.arena.garbage(c) || !self.arena.redundant(c) {
                continue;
            }
            let c_size = self.arena.size(c);
            if c_size <= clause_size {
                continue;
            }
            let mut needed = clause_size;
            let mut remain = c_size;
            for &lit in self.arena.lits(c) {
                if self.marks[lit.idx()] != 0 {
                    needed -= 1;
                    if needed == 0 {
                        break;
                    }
                }
                remain -= 1;
                if remain < needed {
                    break;
                }
            }
            if needed > 0 || self.is_reason(c) {
                continue;
            }
            self.mark_garbage(c);
            self.last_learned[k] = INVALID_REF;
            self.stats.eagerly_subsumed += 1;
        }
        for &lit in &self.clause {
            self.marks[lit.idx()] = 0;
        }
        self.last_learned.sort_by_key(|&c| c == INVALID_REF);
    }

    fn reset_analysis_but_not_analyzed_literals(&mut self) {
        for &v in &self.removable {
            self.assigned[v as usize].flags &= !REMOVABLE;
        }
        self.removable.clear();
        for &level in &self.levels {
            self.frames[level as usize].used = 0;
        }
        self.levels.clear();
        self.clause.clear();
    }

    fn reset_analyzed(&mut self) {
        for &v in &self.analyzed {
            self.assigned[v as usize].flags &= !ANALYZED;
        }
        self.analyzed.clear();
    }

    pub fn update_tier_limits(&mut self) {
        self.stats.retiered += 1;
        self.compute_and_set_tier_limits();
        if self.limits.glue_interval < (1 << 16) {
            self.limits.glue_interval *= 2;
        }
        self.limits.glue_conflicts = self.stats.conflicts + self.limits.glue_interval;
    }

    pub fn compute_and_set_tier_limits(&mut self) {
        let stable = self.stable as usize;
        let used = &self.stats.used[stable];
        let total: u64 = used.iter().sum();
        let mut tier1: i64 = -1;
        let mut tier2: i64 = -1;
        if total > 0 {
            let limit1 = total * self.opts.tier1relative / 1000;
            let limit2 = total * self.opts.tier2relative / 1000;
            let mut acc = 0;
            let mut glue = 0;
            while glue <= MAX_GLUE_USED {
                acc += used[glue];
                if acc >= limit1 {
                    tier1 = glue as i64;
                    break;
                }
                glue += 1;
            }
            if acc < limit2 {
                let mut glue = tier1 as usize + 1;
                while glue <= MAX_GLUE_USED {
                    acc += used[glue];
                    if acc >= limit2 {
                        tier2 = glue as i64;
                        break;
                    }
                    glue += 1;
                }
            }
        }
        if tier1 < 0 {
            tier1 = self.opts.tier1 as i64;
            tier2 = (self.opts.tier2 as i64).max(tier1);
        } else if tier2 < 0 {
            tier2 = tier1;
        }
        self.tier1[stable] = tier1 as u32;
        self.tier2[stable] = tier2 as u32;
    }

    /// Kissat uses the focused tier1 and the stable tier2 limit.
    pub fn tier1_limit(&self) -> u32 {
        self.tier1[0]
    }

    pub fn tier2_limit(&self) -> u32 {
        self.tier2[1].max(self.tier1[0])
    }

    // ------------------------------------------------------------------
    // Bumping.

    fn bump_analyzed(&mut self) {
        if self.stable {
            for i in 0..self.analyzed.len() {
                let v = self.analyzed[i];
                self.bump_variable_score(v);
            }
            self.bump_score_increment();
        } else {
            let mut ranked = std::mem::take(&mut self.analyzed);
            let links = &self.queue.links;
            ranked.sort_unstable_by_key(|&v| links[v as usize].stamp);
            for &v in &ranked {
                let assigned = self.values[Lit::new(v, false).idx()] != 0;
                self.queue.move_to_front(v, assigned);
            }
            self.analyzed = ranked;
        }
    }

    fn bump_variable_score(&mut self, v: Var) {
        let new_score = self.heap.score[v as usize] + self.scinc;
        self.heap.update(v, new_score);
        if new_score > MAX_SCORE {
            self.rescale_scores();
        }
    }

    fn bump_score_increment(&mut self) {
        let decay = self.opts.decay as f64 * 1e-3;
        self.scinc *= 1.0 / (1.0 - decay);
        if self.scinc > MAX_SCORE {
            self.rescale_scores();
        }
    }

    pub fn rescale_scores_now(&mut self) {
        self.rescale_scores();
    }

    fn rescale_scores(&mut self) {
        let max_score = self.heap.max_score().max(self.scinc);
        let factor = 1.0 / max_score;
        self.heap.rescale(factor);
        self.scinc *= factor;
    }
}

enum ConflictLits {
    Binary([Lit; 2]),
    Large(CRef),
}
