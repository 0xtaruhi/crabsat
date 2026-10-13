//! VMTF decision queue (Kissat `queue.c`, `inlinequeue.h`).
//!
//! A doubly linked list of variables ordered by enqueue time ("stamp").
//! The last element was bumped most recently.  `search` caches the position
//! from which the next unassigned variable is searched (towards the front).

use crate::types::Var;

pub const DISCONNECT: u32 = u32::MAX;

#[derive(Copy, Clone)]
pub struct Links {
    pub prev: u32,
    pub next: u32,
    pub stamp: u32,
}

impl Default for Links {
    fn default() -> Self {
        Links { prev: DISCONNECT, next: DISCONNECT, stamp: 0 }
    }
}

pub struct Queue {
    pub links: Vec<Links>,
    pub first: u32,
    pub last: u32,
    pub stamp: u32,
    pub search_idx: u32,
    pub search_stamp: u32,
}

impl Default for Queue {
    fn default() -> Self {
        Queue {
            links: Vec::new(),
            first: DISCONNECT,
            last: DISCONNECT,
            stamp: 0,
            search_idx: DISCONNECT,
            search_stamp: 0,
        }
    }
}

impl Queue {
    #[inline]
    pub fn update_search(&mut self, idx: u32) {
        self.search_idx = idx;
        self.search_stamp = self.links[idx as usize].stamp;
    }

    pub fn reassign_stamps(&mut self) {
        self.stamp = 0;
        let mut idx = self.first;
        while idx != DISCONNECT {
            self.stamp += 1;
            self.links[idx as usize].stamp = self.stamp;
            idx = self.links[idx as usize].next;
        }
        if self.search_idx != DISCONNECT {
            self.search_stamp = self.links[self.search_idx as usize].stamp;
        }
    }

    fn enqueue_links(&mut self, i: u32) {
        let j = self.last;
        self.links[i as usize].prev = j;
        self.links[i as usize].next = DISCONNECT;
        self.last = i;
        if j == DISCONNECT {
            self.first = i;
        } else {
            self.links[j as usize].next = i;
        }
        if self.stamp == u32::MAX {
            self.reassign_stamps();
        } else {
            self.stamp += 1;
            self.links[i as usize].stamp = self.stamp;
        }
    }

    fn dequeue_links(&mut self, i: u32) {
        let l = self.links[i as usize];
        let (j, k) = (l.prev, l.next);
        self.links[i as usize].prev = DISCONNECT;
        self.links[i as usize].next = DISCONNECT;
        if j == DISCONNECT {
            self.first = k;
        } else {
            self.links[j as usize].next = k;
        }
        if k == DISCONNECT {
            self.last = j;
        } else {
            self.links[k as usize].prev = j;
        }
    }

    /// Append a new variable; `unassigned` tells whether it may be decided.
    pub fn enqueue(&mut self, idx: Var, unassigned: bool) {
        if self.links.len() <= idx as usize {
            self.links.resize(idx as usize + 1, Links::default());
        }
        self.enqueue_links(idx);
        if unassigned {
            self.update_search(idx);
        }
    }

    /// Insert a (dequeued) variable at the front, i.e., with lowest
    /// priority.  Stamps have to be reassigned afterwards.
    pub fn push_front(&mut self, idx: Var) {
        let first = self.first;
        self.links[idx as usize].prev = DISCONNECT;
        self.links[idx as usize].next = first;
        if first == DISCONNECT {
            self.last = idx;
        } else {
            self.links[first as usize].prev = idx;
        }
        self.first = idx;
    }

    /// Rebuild the queue with the variables in the given order (the last
    /// one is the first decision candidate).
    pub fn rebuild(&mut self, order: &[Var]) {
        self.first = DISCONNECT;
        self.last = DISCONNECT;
        self.stamp = 0;
        self.search_idx = DISCONNECT;
        for &v in order {
            self.enqueue_links(v);
        }
        self.reset_search();
    }

    /// Remove a variable from the queue (eliminated / fixed).
    pub fn dequeue(&mut self, idx: Var) {
        if self.search_idx == idx {
            let l = self.links[idx as usize];
            let search = if l.next != DISCONNECT { l.next } else { l.prev };
            if search == DISCONNECT {
                self.search_idx = DISCONNECT;
                self.search_stamp = 0;
            } else {
                self.update_search(search);
            }
        }
        self.dequeue_links(idx);
    }

    /// Move `idx` to the end of the queue (bump).  `assigned` is its current
    /// assignment status.
    pub fn move_to_front(&mut self, idx: Var, assigned: bool) {
        if idx == self.last {
            return;
        }
        if assigned && self.search_idx == idx {
            let l = self.links[idx as usize];
            if l.prev != DISCONNECT {
                self.update_search(l.prev);
            } else {
                self.update_search(l.next);
            }
        }
        self.dequeue_links(idx);
        self.enqueue_links(idx);
        if !assigned {
            self.update_search(idx);
        }
    }

    pub fn reset_search(&mut self) {
        if self.last != DISCONNECT {
            self.update_search(self.last);
        }
    }
}
