//! Clause arena (Kissat `arena.c` / `clause.h`).
//!
//! Large clauses (size >= 3) live consecutively in one `Vec<u32>` and are
//! referenced by their word offset (`CRef`).  Binary clauses are never stored
//! here; they only exist as binary watches.
//!
//! Layout of a clause at offset `c`:
//!
//! ```text
//! mem[c]     flags: glue (19 bits) | garbage | reason | redundant | shrunken
//!                   | subsume | vivify | used (5 bits)
//! mem[c + 1] searched position (>= 2)
//! mem[c + 2] size
//! mem[c + 3 ..] literals
//! ```
//!
//! A clause which was shrunken in place is padded with `INVALID` literals so
//! that the arena can still be traversed linearly.

use crate::types::Lit;

pub type CRef = u32;

pub const INVALID_REF: CRef = u32::MAX;
pub const HEADER: usize = 3;

pub const MAX_GLUE: u32 = (1 << 19) - 1;
pub const MAX_USED: u32 = (1 << 5) - 1;

const GLUE_MASK: u32 = MAX_GLUE;
pub const GARBAGE: u32 = 1 << 19;
const REASON: u32 = 1 << 20;
const REDUNDANT: u32 = 1 << 21;
const SHRUNKEN: u32 = 1 << 22;
const SUBSUME: u32 = 1 << 23;
const VIVIFY: u32 = 1 << 24;
const USED_SHIFT: u32 = 27;
const USED_MASK: u32 = MAX_USED << USED_SHIFT;

const INVALID_LIT: u32 = u32::MAX;

#[derive(Default, Clone)]
pub struct Arena {
    pub mem: Vec<u32>,
}

macro_rules! flag {
    ($get:ident, $set:ident, $bit:expr) => {
        #[inline(always)]
        pub fn $get(&self, c: CRef) -> bool {
            self.mem[c as usize] & $bit != 0
        }
        #[inline(always)]
        pub fn $set(&mut self, c: CRef, value: bool) {
            let w = &mut self.mem[c as usize];
            if value { *w |= $bit } else { *w &= !$bit }
        }
    };
}

impl Arena {
    pub fn len(&self) -> usize {
        self.mem.len()
    }

    pub fn is_empty(&self) -> bool {
        self.mem.is_empty()
    }

    /// Allocate a new clause.  The first two literals are the watched ones.
    pub fn alloc(&mut self, lits: &[Lit], redundant: bool, glue: u32) -> CRef {
        debug_assert!(lits.len() >= 3);
        let c = self.mem.len();
        assert!(c + HEADER + lits.len() < u32::MAX as usize, "arena overflow");
        let mut flags = glue.min(MAX_GLUE);
        if redundant {
            flags |= REDUNDANT;
        }
        self.mem.push(flags);
        self.mem.push(2);
        self.mem.push(lits.len() as u32);
        self.mem.extend(lits.iter().map(|l| l.0));
        c as CRef
    }

    #[inline(always)]
    pub fn size(&self, c: CRef) -> usize {
        self.mem[c as usize + 2] as usize
    }

    #[inline(always)]
    pub fn lits(&self, c: CRef) -> &[Lit] {
        let start = c as usize + HEADER;
        let size = self.size(c);
        let words = &self.mem[start..start + size];
        // SAFETY: `Lit` is `repr(transparent)` over `u32`.
        unsafe { std::slice::from_raw_parts(words.as_ptr() as *const Lit, size) }
    }

    #[inline(always)]
    pub fn lits_mut(&mut self, c: CRef) -> &mut [Lit] {
        let start = c as usize + HEADER;
        let size = self.size(c);
        let words = &mut self.mem[start..start + size];
        // SAFETY: `Lit` is `repr(transparent)` over `u32`.
        unsafe { std::slice::from_raw_parts_mut(words.as_mut_ptr() as *mut Lit, size) }
    }

    #[inline(always)]
    pub fn glue(&self, c: CRef) -> u32 {
        self.mem[c as usize] & GLUE_MASK
    }

    #[inline(always)]
    pub fn set_glue(&mut self, c: CRef, glue: u32) {
        let w = &mut self.mem[c as usize];
        *w = (*w & !GLUE_MASK) | glue.min(MAX_GLUE);
    }

    #[inline(always)]
    pub fn used(&self, c: CRef) -> u32 {
        (self.mem[c as usize] & USED_MASK) >> USED_SHIFT
    }

    #[inline(always)]
    pub fn set_used(&mut self, c: CRef, used: u32) {
        debug_assert!(used <= MAX_USED);
        let w = &mut self.mem[c as usize];
        *w = (*w & !USED_MASK) | (used << USED_SHIFT);
    }

    flag!(garbage, set_garbage, GARBAGE);
    flag!(reason, set_reason, REASON);
    flag!(redundant, set_redundant, REDUNDANT);
    flag!(subsume, set_subsume, SUBSUME);
    flag!(vivify, set_vivify, VIVIFY);

    #[inline(always)]
    pub fn searched(&self, c: CRef) -> usize {
        self.mem[c as usize + 1] as usize
    }

    #[inline(always)]
    pub fn set_searched(&mut self, c: CRef, pos: usize) {
        self.mem[c as usize + 1] = pos as u32;
    }

    /// Shrink a clause in place to `new_size` literals (>= 3), padding the
    /// freed words so that linear traversal still works.
    pub fn shrink(&mut self, c: CRef, new_size: usize) {
        let old_size = self.size(c);
        debug_assert!(3 <= new_size && new_size <= old_size);
        if new_size == old_size {
            return;
        }
        let start = c as usize + HEADER;
        for w in &mut self.mem[start + new_size..start + old_size] {
            *w = INVALID_LIT;
        }
        self.mem[c as usize + 2] = new_size as u32;
        self.mem[c as usize] |= SHRUNKEN;
        if self.searched(c) >= new_size {
            self.set_searched(c, 2);
        }
    }

    /// Offset of the clause following `c`.
    #[inline]
    pub fn next(&self, c: CRef) -> CRef {
        let mut end = c as usize + HEADER + self.size(c);
        if self.mem[c as usize] & SHRUNKEN != 0 {
            while end < self.mem.len() && self.mem[end] == INVALID_LIT {
                end += 1;
            }
        }
        end as CRef
    }

    /// Clear the shrunken flag (after the clause has been moved).
    #[inline]
    pub fn clear_shrunken(&mut self, c: CRef) {
        self.mem[c as usize] &= !SHRUNKEN;
    }

    /// Iterate over all clause references starting at `start`.
    pub fn refs_from(&self, start: CRef) -> ArenaIter<'_> {
        ArenaIter { arena: self, pos: start }
    }
}

pub struct ArenaIter<'a> {
    arena: &'a Arena,
    pos: CRef,
}

impl Iterator for ArenaIter<'_> {
    type Item = CRef;
    fn next(&mut self) -> Option<CRef> {
        if self.pos as usize >= self.arena.mem.len() {
            return None;
        }
        let c = self.pos;
        self.pos = self.arena.next(c);
        Some(c)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lits(ds: &[i32]) -> Vec<Lit> {
        ds.iter().map(|&d| Lit::from_dimacs(d)).collect()
    }

    #[test]
    fn alloc_and_flags() {
        let mut a = Arena::default();
        let c = a.alloc(&lits(&[1, -2, 3]), true, 5);
        let d = a.alloc(&lits(&[4, 5, 6, 7]), false, 0);
        assert_eq!(a.size(c), 3);
        assert_eq!(a.glue(c), 5);
        assert!(a.redundant(c) && !a.redundant(d));
        a.set_used(c, MAX_USED);
        a.set_garbage(c, true);
        assert_eq!(a.used(c), MAX_USED);
        assert_eq!(a.glue(c), 5);
        assert!(a.garbage(c));
        a.set_glue(c, 2);
        assert_eq!(a.used(c), MAX_USED);
        assert_eq!(a.refs_from(0).collect::<Vec<_>>(), vec![c, d]);
        a.shrink(d, 3);
        let e = a.alloc(&lits(&[8, 9, 10]), false, 0);
        assert_eq!(a.refs_from(0).collect::<Vec<_>>(), vec![c, d, e]);
        assert_eq!(a.lits(d), &lits(&[4, 5, 6])[..]);
    }
}
