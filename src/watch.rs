//! Watch lists (Kissat `watch.h`).
//!
//! Each literal has a vector of 32-bit words.  A binary watch is a single
//! word holding the other literal with the `BINARY` bit set.  A large watch
//! takes two words: the blocking literal (without the bit) followed by the
//! clause reference.

use crate::arena::CRef;
use crate::types::Lit;

pub const BINARY: u32 = 1 << 31;

pub type WatchList = Vec<u32>;

#[inline(always)]
pub fn is_binary(head: u32) -> bool {
    head & BINARY != 0
}

#[inline(always)]
pub fn head_lit(head: u32) -> Lit {
    Lit(head & !BINARY)
}

#[inline(always)]
pub fn push_binary(ws: &mut WatchList, other: Lit) {
    ws.push(other.0 | BINARY);
}

#[inline(always)]
pub fn push_large(ws: &mut WatchList, blocking: Lit, c: CRef) {
    ws.push(blocking.0);
    ws.push(c);
}

/// Remove the binary watch `other` from `ws`.
pub fn remove_binary(ws: &mut WatchList, other: Lit) {
    let target = other.0 | BINARY;
    let mut i = 0;
    while i < ws.len() {
        let head = ws[i];
        if is_binary(head) {
            if head == target {
                ws.remove(i);
                return;
            }
            i += 1;
        } else {
            i += 2;
        }
    }
    debug_assert!(false, "binary watch not found");
}

/// Remove the large watch of clause `c` from `ws`.
pub fn remove_large(ws: &mut WatchList, c: CRef) {
    let mut i = 0;
    while i < ws.len() {
        if is_binary(ws[i]) {
            i += 1;
        } else {
            if ws[i + 1] == c {
                ws.drain(i..i + 2);
                return;
            }
            i += 2;
        }
    }
    debug_assert!(false, "large watch not found");
}

/// Iterate over a watch list, yielding decoded watches.
pub enum Watch {
    Binary(Lit),
    Large(CRef),
}

pub(crate) fn iter(ws: &WatchList) -> impl Iterator<Item = Watch> + '_ {
    let mut i = 0;
    std::iter::from_fn(move || {
        if i >= ws.len() {
            return None;
        }
        let head = ws[i];
        if is_binary(head) {
            i += 1;
            Some(Watch::Binary(head_lit(head)))
        } else {
            i += 2;
            Some(Watch::Large(ws[i - 1]))
        }
    })
}
