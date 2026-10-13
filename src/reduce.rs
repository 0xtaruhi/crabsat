//! Learned clause reduction and arena garbage collection (Kissat
//! `reduce.c`, `collect.c`).

use crate::arena::{CRef, HEADER, INVALID_REF, MAX_USED};
use crate::solver::{BINARY, Solver};
use crate::types::Lit;
use crate::watch;

impl Solver {
    pub fn reducing(&self) -> bool {
        self.opts.reduce
            && self.stats.clauses_redundant > 0
            && self.stats.conflicts >= self.limits.reduce_conflicts
    }

    pub fn reduce(&mut self) {
        let start = std::time::Instant::now();
        self.reduce_untimed();
        self.stats.time_reduce += start.elapsed().as_secs_f64();
    }

    fn reduce_untimed(&mut self) {
        self.stats.reductions += 1;
        self.compute_and_set_tier_limits();
        // Remove root-satisfied clauses if new units were found.
        let fixed = self.stats.units;
        let full = fixed != self.fixed_at_last_collect;
        let start = if full { 0 } else { self.first_reducible };
        if start != INVALID_REF {
            self.mark_reason_clauses(true);
            if full {
                self.fixed_at_last_collect = fixed;
                self.mark_satisfied_clauses_as_garbage();
            }
            self.mark_less_useful_clauses_as_garbage(start);
            // Collection redirects and clears the reason flags of moved
            // clauses; flags of clauses before `start` are cleared here.
            self.collect(start, full);
            self.mark_reason_clauses(false);
        }
        let delta = self.opts.reduceint as f64 * (self.stats.reductions as f64).sqrt();
        self.limits.reduce_conflicts = self.stats.conflicts + delta as u64;
        self.report('-');
    }

    /// Set or clear the reason flag of all clauses that are reasons.
    fn mark_reason_clauses(&mut self, value: bool) {
        for i in 0..self.trail.len() {
            let lit = self.trail[i];
            let a = self.assigned[lit.vidx()];
            if a.level == 0 || a.has(BINARY) {
                continue;
            }
            if a.reason == crate::solver::DECISION_REASON {
                continue;
            }
            self.arena.set_reason(a.reason, value);
        }
    }

    fn mark_satisfied_clauses_as_garbage(&mut self) {
        let mut c = 0;
        while (c as usize) < self.arena.len() {
            let next = self.arena.next(c);
            if !self.arena.garbage(c) && !self.arena.reason(c) {
                let satisfied = self.arena.lits(c).iter().any(|&l| self.fixed(l) > 0);
                if satisfied {
                    self.mark_garbage(c);
                }
            }
            c = next;
        }
    }

    fn mark_less_useful_clauses_as_garbage(&mut self, start: CRef) {
        let tier1 = self.tier1_limit();
        let tier2 = self.tier2_limit();
        let mut reducibles: Vec<(u64, CRef)> = Vec::new();
        let mut c = start;
        while (c as usize) < self.arena.len() {
            let next = self.arena.next(c);
            if self.arena.redundant(c) && !self.arena.garbage(c) {
                let used = self.arena.used(c);
                if used > 0 {
                    self.arena.set_used(c, used - 1);
                }
                let glue = self.arena.glue(c);
                let keep = self.arena.reason(c)
                    || (glue <= tier1 && used > 0)
                    || (glue <= tier2 && used >= MAX_USED - 1);
                if !keep {
                    let size = self.arena.size(c) as u64;
                    let rank = (!(glue as u64) << 32) | (!size & 0xffff_ffff);
                    reducibles.push((rank, c));
                }
            }
            c = next;
        }
        if reducibles.is_empty() {
            return;
        }
        reducibles.sort_unstable_by_key(|r| r.0);
        let high = self.opts.reducehigh as f64 * 0.1;
        let low = self.opts.reducelow as f64 * 0.1;
        let percent = if low < high {
            high - (high - low) / ((self.stats.reductions + 9) as f64).log10()
        } else {
            low
        };
        let target = (reducibles.len() as f64 * percent / 100.0) as usize;
        for &(_, c) in &reducibles[..target] {
            self.mark_garbage(c);
            self.stats.clauses_reduced += 1;
        }
    }

    /// Compact the arena from `start`, updating watches and reasons.  With
    /// `full` also flush satisfied binary clauses.
    pub fn collect(&mut self, start: CRef, full: bool) {
        self.stats.collections += 1;
        // Flush watches of large clauses at or after `start`.
        for lit_idx in 0..self.watches.len() {
            let lit = Lit(lit_idx as u32);
            let lit_fixed = self.fixed(lit);
            let mut ws = std::mem::take(&mut self.watches[lit_idx]);
            let mut j = 0;
            let mut i = 0;
            while i < ws.len() {
                let head = ws[i];
                if watch::is_binary(head) {
                    i += 1;
                    let other = watch::head_lit(head);
                    if full && (lit_fixed > 0 || self.fixed(other) > 0) {
                        if lit < other {
                            self.stats.clauses_binary -= 1;
                            if let Some(p) = self.proof.as_mut() {
                                p.delete(&[lit, other]);
                            }
                        }
                        continue;
                    }
                    ws[j] = head;
                    j += 1;
                } else {
                    let c = ws[i + 1];
                    i += 2;
                    if c < start {
                        ws[j] = head;
                        ws[j + 1] = c;
                        j += 2;
                    }
                }
            }
            ws.truncate(j);
            self.watches[lit_idx] = ws;
        }
        // Move clauses down.
        let mut dst = start as usize;
        let mut src = start;
        let mut first_reducible = if self.first_reducible < start {
            self.first_reducible
        } else {
            INVALID_REF
        };
        let len = self.arena.len();
        while (src as usize) < len {
            let next = self.arena.next(src);
            if !self.arena.garbage(src) {
                let size = self.arena.size(src);
                let words = HEADER + size;
                let s = src as usize;
                self.arena.mem.copy_within(s..s + words, dst);
                let c = dst as CRef;
                self.arena.clear_shrunken(c);
                if self.arena.reason(c) {
                    // Find the forced (true) literal and redirect its reason.
                    let forced = *self
                        .arena
                        .lits(c)
                        .iter()
                        .find(|&&l| self.value(l) > 0)
                        .expect("reason clause without true literal");
                    self.assigned[forced.vidx()].reason = c;
                    self.arena.set_reason(c, false);
                }
                if first_reducible == INVALID_REF && self.arena.redundant(c) {
                    first_reducible = c;
                }
                dst += words;
            }
            src = next;
        }
        self.arena.mem.truncate(dst);
        self.first_reducible = first_reducible;
        for l in self.last_learned.iter_mut() {
            *l = INVALID_REF;
        }
        // Re-watch moved clauses.
        let mut c = start;
        while (c as usize) < self.arena.len() {
            self.watch_clause(c);
            c = self.arena.next(c);
        }
    }
}
