//! Backtracking (Kissat `backtrack.c`).  With chronological backtracking
//! literals on lower levels than the target level may sit above it on the
//! trail; those are kept (and re-propagated).

use crate::solver::Solver;

impl Solver {
    fn update_target_and_best_phases(&mut self) {
        if !self.stable || self.probing {
            return;
        }
        let assigned = self.assigned_count();
        if self.target_assigned < assigned {
            self.target_assigned = assigned;
            save_phases(&self.values, &mut self.phases.target);
        }
        if self.best_assigned < assigned {
            self.best_assigned = assigned;
            save_phases(&self.values, &mut self.phases.best);
        }
    }

    pub fn backtrack_without_updating_phases(&mut self, new_level: u32) {
        if self.level == new_level {
            return;
        }
        debug_assert!(new_level < self.level);
        let new_end = self.frames[new_level as usize + 1].trail as usize;
        self.frames.truncate(new_level as usize + 1);
        let mut q = new_end;
        for p in new_end..self.trail.len() {
            let lit = self.trail[p];
            let v = lit.var();
            let a = &mut self.assigned[v as usize];
            if a.level <= new_level {
                a.trail = q as u32;
                self.trail[q] = lit;
                q += 1;
            } else {
                self.values[lit.idx()] = 0;
                self.values[(!lit).idx()] = 0;
                self.unassigned += 1;
                if self.stable {
                    if !self.heap.contains(v) {
                        self.heap.push(v);
                    }
                } else if self.queue.links[v as usize].stamp > self.queue.search_stamp {
                    self.queue.update_search(v);
                }
            }
        }
        self.trail.truncate(q);
        self.level = new_level;
        self.propagated = new_end;
    }

    pub fn backtrack_in_consistent_state(&mut self, new_level: u32) {
        self.update_target_and_best_phases();
        self.backtrack_without_updating_phases(new_level);
    }

    pub fn backtrack_after_conflict(&mut self, new_level: u32) {
        if self.level > 0 {
            self.backtrack_without_updating_phases(self.level - 1);
        }
        self.update_target_and_best_phases();
        self.backtrack_without_updating_phases(new_level);
    }

    /// Backtrack to the root and propagate (used before rephasing and
    /// simplification).  Returns false on root-level conflict.
    pub fn backtrack_propagate_root(&mut self) -> bool {
        if self.level > 0 {
            self.backtrack_in_consistent_state(0);
        }
        if self.propagate().is_some() {
            self.mark_inconsistent();
        }
        !self.inconsistent
    }
}

fn save_phases(values: &[i8], phases: &mut [i8]) {
    for (p, pair) in phases.iter_mut().zip(values.chunks_exact(2)) {
        if pair[0] != 0 {
            *p = pair[0];
        }
    }
}
