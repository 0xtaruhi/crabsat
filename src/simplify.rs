//! Root-level clause simplification and switching between watching
//! (sparse) and full occurrence list (dense) mode (Kissat `dense.c`,
//! `collect.c`).
//!
//! In dense mode every irredundant large clause is "connected" with a large
//! watch in the list of each of its literals (the blocking literal is the
//! literal itself and unused).  Binary clauses stay as binary watches.
//! Redundant large clauses are disconnected.

use crate::arena::CRef;
use crate::solver::{ELIMINATED, Solver};
use crate::types::Lit;
use crate::watch;

/// Outcome of simplifying a clause at the root level.
#[derive(PartialEq, Eq, Debug)]
pub enum Simplified {
    /// Still a large clause (possibly shrunken).
    Large,
    /// Removed (satisfied, or turned into a binary or unit clause).
    Removed,
}

impl Solver {
    /// Remove root-falsified literals of `c` and delete it if satisfied.
    /// Must be called at level 0 when `c` is not a reason.
    pub fn simplify_clause_at_root(&mut self, c: CRef) -> Simplified {
        debug_assert_eq!(self.level, 0);
        debug_assert!(!self.arena.garbage(c));
        let mut falsified = 0;
        for &lit in self.arena.lits(c) {
            let v = self.fixed(lit);
            if v > 0 {
                self.mark_garbage(c);
                return Simplified::Removed;
            }
            if v < 0 {
                falsified += 1;
            }
        }
        if falsified == 0 {
            return Simplified::Large;
        }
        let lits: Vec<Lit> = self
            .arena
            .lits(c)
            .iter()
            .copied()
            .filter(|&l| self.fixed(l) == 0)
            .collect();
        self.strengthen_to(c, &lits)
    }

    /// Replace clause `c` by the clause `lits` (a subset of its literals),
    /// producing a binary clause, unit or empty clause if necessary.
    pub fn strengthen_to(&mut self, c: CRef, lits: &[Lit]) -> Simplified {
        self.trace("strengthen-from", self.arena.lits(c));
        if let Some(p) = self.proof.as_mut() {
            p.add(lits);
        }
        match lits.len() {
            0 => {
                self.mark_garbage(c);
                self.mark_inconsistent();
                Simplified::Removed
            }
            1 => {
                self.mark_garbage(c);
                if self.value(lits[0]) == 0 {
                    self.assign_unit(lits[0]);
                } else if self.value(lits[0]) < 0 {
                    self.mark_inconsistent();
                }
                Simplified::Removed
            }
            2 => {
                self.mark_garbage(c);
                self.new_binary(lits[0], lits[1]);
                Simplified::Removed
            }
            _ => {
                if let Some(p) = self.proof.as_mut() {
                    p.delete(self.arena.lits(c));
                }
                let size = lits.len();
                self.arena.lits_mut(c)[..size].copy_from_slice(lits);
                self.arena.shrink(c, size);
                if !self.arena.redundant(c) {
                    for &l in lits {
                        self.mark_added_var(l.vidx());
                    }
                }
                Simplified::Large
            }
        }
    }

    /// Switch to dense mode: connect all irredundant large clauses with full
    /// occurrence lists.  Requires level 0 and complete propagation.
    pub fn enter_dense_mode(&mut self) {
        debug_assert_eq!(self.level, 0);
        debug_assert!(!self.dense);
        self.dense = true;
        self.flush_large_watches_and_satisfied_binaries();
        let mut c = 0;
        while (c as usize) < self.arena.len() {
            let next = self.arena.next(c);
            if !self.arena.garbage(c) && !self.arena.redundant(c) {
                if self.simplify_clause_at_root(c) == Simplified::Large {
                    self.connect_occurrences(c);
                }
                if self.inconsistent {
                    return;
                }
            }
            c = next;
        }
    }

    pub fn connect_occurrences(&mut self, c: CRef) {
        for i in 0..self.arena.size(c) {
            let lit = self.arena.lits(c)[i];
            watch::push_large(&mut self.watches[lit.idx()], lit, c);
        }
    }

    /// Remove all large watches and root-satisfied binary clauses.
    fn flush_large_watches_and_satisfied_binaries(&mut self) {
        for idx in 0..self.watches.len() {
            let lit = Lit(idx as u32);
            let lit_fixed = self.fixed(lit);
            let mut ws = std::mem::take(&mut self.watches[idx]);
            let mut j = 0;
            let mut i = 0;
            while i < ws.len() {
                let head = ws[i];
                if watch::is_binary(head) {
                    i += 1;
                    let other = watch::head_lit(head);
                    if lit_fixed > 0 || self.fixed(other) > 0 {
                        if lit < other {
                            self.stats.clauses_binary -= 1;
                            self.mark_removed_var(lit.vidx());
                            self.mark_removed_var(other.vidx());
                            if let Some(p) = self.proof.as_mut() {
                                p.delete(&[lit, other]);
                            }
                        }
                        continue;
                    }
                    ws[j] = head;
                    j += 1;
                } else {
                    i += 2;
                }
            }
            ws.truncate(j);
            self.watches[idx] = ws;
        }
    }

    /// Leave dense mode: delete redundant clauses with eliminated variables,
    /// simplify all clauses at the root, collect the arena and watch again.
    pub fn resume_sparse_mode(&mut self) {
        debug_assert!(self.dense);
        self.dense = false;
        if !self.inconsistent {
            // Propagate units found in dense mode over binary clauses (large
            // clauses are handled by root simplification below).
            self.dense_propagate();
        }
        self.flush_large_watches_and_satisfied_binaries();
        let mut c = 0;
        while (c as usize) < self.arena.len() && !self.inconsistent {
            let next = self.arena.next(c);
            if !self.arena.garbage(c) {
                let eliminated = self.arena.redundant(c)
                    && self
                        .arena
                        .lits(c)
                        .iter()
                        .any(|l| self.flags[l.vidx()] & ELIMINATED != 0);
                if eliminated {
                    self.mark_garbage(c);
                } else {
                    self.simplify_clause_at_root(c);
                }
            }
            c = next;
        }
        self.fixed_at_last_collect = self.stats.units;
        self.collect(0, false);
        self.flush_pending_units();
        if !self.inconsistent && self.propagate().is_some() {
            self.mark_inconsistent();
        }
    }

    /// Unit propagation in dense mode.  Large clauses are connected through
    /// full occurrence lists; returns false on conflict.
    pub fn dense_propagate(&mut self) -> bool {
        while self.propagated < self.trail.len() && !self.inconsistent {
            let lit = self.trail[self.propagated];
            self.propagated += 1;
            let not_lit = !lit;
            let ws = std::mem::take(&mut self.watches[not_lit.idx()]);
            for w in watch::iter(&ws) {
                match w {
                    watch::Watch::Binary(other) => {
                        let v = self.value(other);
                        if v < 0 {
                            self.mark_inconsistent();
                            break;
                        }
                        if v == 0 {
                            self.learned_unit(other);
                        }
                    }
                    watch::Watch::Large(_, c) => {
                        if self.arena.garbage(c) {
                            continue;
                        }
                        let mut unit = Lit::INVALID;
                        let mut unassigned = 0;
                        let mut satisfied = false;
                        for &l in self.arena.lits(c) {
                            let v = self.value(l);
                            if v > 0 {
                                satisfied = true;
                                break;
                            }
                            if v == 0 {
                                unassigned += 1;
                                unit = l;
                            }
                        }
                        if satisfied || unassigned > 1 {
                            continue;
                        }
                        if unassigned == 0 {
                            self.mark_inconsistent();
                            break;
                        }
                        self.learned_unit(unit);
                    }
                }
            }
            self.watches[not_lit.idx()] = ws;
        }
        self.flush_pending_units();
        !self.inconsistent
    }
}
