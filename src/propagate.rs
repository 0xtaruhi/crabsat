//! Unit propagation (Kissat `proplit.h`).
//!
//! Large clauses keep their two watched literals at positions 0 and 1, so
//! the other watched literal is `lits[0] ^ lits[1] ^ not_lit`.  Replacement
//! search starts at the saved `searched` position (Gent).  New watches are
//! delayed until the current watch list has been traversed.

use crate::arena::{GARBAGE, HEADER};
use crate::solver::{Assigned, Conflict, Solver, BINARY, UNIT_REASON};
use crate::types::Lit;
use crate::watch;

/// Unchecked indexing in release builds, checked in debug builds.
macro_rules! at {
    ($s:expr, $i:expr) => {{
        let i = $i;
        debug_assert!(i < $s.len());
        unsafe { *$s.get_unchecked(i) }
    }};
}

macro_rules! at_mut {
    ($s:expr, $i:expr) => {{
        let i = $i;
        debug_assert!(i < $s.len());
        unsafe { $s.get_unchecked_mut(i) }
    }};
}

impl Solver {
    /// Propagate all literals on the trail.  Returns a conflict if found.
    pub fn propagate(&mut self) -> Option<Conflict> {
        let before = self.propagated;
        let mut conflict = None;
        while self.propagated < self.trail.len() {
            let lit = self.trail[self.propagated];
            self.propagated += 1;
            if let Some(c) = self.propagate_literal(lit) {
                conflict = Some(c);
                break;
            }
        }
        self.stats.propagations += (self.propagated - before) as u64;
        if !self.pending_units.is_empty() {
            self.flush_pending_units();
        }
        if conflict.is_some() {
            if !self.probing && !self.warming {
                self.stats.conflicts += 1;
            }
            if self.level == 0 {
                self.mark_inconsistent();
            }
        }
        conflict
    }

    #[inline]
    fn propagate_literal(&mut self, lit: Lit) -> Option<Conflict> {
        let not_lit = !lit;
        let level = self.assigned[lit.vidx()].level;
        let current_level = self.level;
        let probing = self.probing;
        let ignore = self.ignore;
        let Solver {
            values,
            assigned,
            trail,
            watches,
            arena,
            delayed,
            phases,
            unassigned,
            pending_units,
            stats,
            ..
        } = self;
        let mem = &mut arena.mem;
        let saved = &mut phases.saved;
        debug_assert!(delayed.is_empty());

        // Assign `$lit` at `$level` with the given reason.
        macro_rules! assign {
            ($lit:expr, $level:expr, $binary:expr, $reason:expr) => {{
                let l: Lit = $lit;
                let lvl: u32 = $level;
                let (reason, flags) = if lvl == 0 {
                    pending_units.push(l);
                    stats.units += 1;
                    (UNIT_REASON, 0)
                } else {
                    ($reason, if $binary { BINARY } else { 0 })
                };
                *at_mut!(values, l.idx()) = 1;
                *at_mut!(values, (!l).idx()) = -1;
                *unassigned -= 1;
                if !probing {
                    *at_mut!(saved, l.vidx()) = if l.negated() { -1 } else { 1 };
                }
                *at_mut!(assigned, l.vidx()) =
                    Assigned { level: lvl, trail: trail.len() as u32, reason, flags };
                trail.push(l);
            }};
        }

        let ws = &mut watches[not_lit.idx()];
        let n = ws.len();
        let mut ticks = 1 + (n as u64 * 4).div_ceil(64);
        let (mut i, mut j) = (0usize, 0usize);
        let mut res = None;
        while i < n {
            let head = at!(ws, i);
            *at_mut!(ws, j) = head;
            i += 1;
            j += 1;
            let binary = watch::is_binary(head);
            let blocking = watch::head_lit(head);
            let blocking_value = at!(values, blocking.idx());
            let mut tail = 0;
            if !binary {
                tail = at!(ws, i);
                *at_mut!(ws, j) = tail;
                i += 1;
                j += 1;
            }
            if blocking_value > 0 {
                continue;
            }
            if binary {
                if blocking_value < 0 {
                    res = Some(Conflict::Binary(not_lit, blocking));
                    break;
                }
                assign!(blocking, level, true, not_lit.0);
                ticks += 1;
                continue;
            }
            let c = tail as usize;
            ticks += 1;
            if at!(mem, c) & GARBAGE != 0 {
                // Garbage clause: drop the watch.
                j -= 2;
                continue;
            }
            let base = c + HEADER;
            let l0 = at!(mem, base);
            let l1 = at!(mem, base + 1);
            let other = Lit(l0 ^ l1 ^ not_lit.0);
            let other_value = at!(values, other.idx());
            if other_value > 0 {
                *at_mut!(ws, j - 2) = other.0;
                continue;
            }
            let size = at!(mem, c + 2) as usize;
            let searched = at!(mem, c + 1) as usize;
            let mut r = searched;
            let mut replacement = 0u32;
            let mut replacement_value: i8 = -1;
            while r < size {
                replacement = at!(mem, base + r);
                replacement_value = at!(values, replacement as usize);
                if replacement_value >= 0 {
                    break;
                }
                r += 1;
            }
            if replacement_value < 0 {
                r = 2;
                while r < searched {
                    replacement = at!(mem, base + r);
                    replacement_value = at!(values, replacement as usize);
                    if replacement_value >= 0 {
                        break;
                    }
                    r += 1;
                }
            }
            if replacement_value >= 0 {
                *at_mut!(mem, c + 1) = r as u32;
                j -= 2;
                *at_mut!(mem, base) = other.0;
                *at_mut!(mem, base + 1) = replacement;
                *at_mut!(mem, base + r) = not_lit.0;
                delayed.push(replacement);
                delayed.push(other.0);
                delayed.push(tail);
                ticks += 1;
            } else if tail == ignore {
                // The clause being vivified must not propagate.
            } else if other_value != 0 {
                res = Some(Conflict::Large(tail));
                break;
            } else {
                // The assignment level is the maximum level of the other
                // (false) literals, which is at most the current level.
                let lvl = if level == current_level {
                    level
                } else {
                    let mut m = 0;
                    for k in 0..size {
                        let l = Lit(at!(mem, base + k));
                        if l != other {
                            m = m.max(at!(assigned, l.vidx()).level);
                        }
                    }
                    m
                };
                assign!(other, lvl, false, tail);
                ticks += 1;
            }
        }
        while i < n {
            *at_mut!(ws, j) = at!(ws, i);
            i += 1;
            j += 1;
        }
        ws.truncate(j);
        if probing {
            stats.probing_ticks += ticks;
        } else {
            stats.search_ticks += ticks;
        }
        for d in delayed.chunks_exact(3) {
            let ws = &mut watches[d[0] as usize];
            ws.push(d[1]);
            ws.push(d[2]);
        }
        delayed.clear();
        res
    }
}
