//! Compacting variable renumbering (Kissat `compact.c`).
//!
//! Eliminated and root-level fixed variables are removed from all internal
//! data structures and the remaining (active) variables are renumbered
//! densely, which keeps per-variable arrays and watch lists small and cache
//! friendly.  External variables keep their numbers: `e2i`/`i2e` map
//! between both, fixed values are kept in `ext_fixed` and the extension
//! stack uses external literals.

use crate::arena::{HEADER, INVALID_REF};
use crate::heap::Heap;
use crate::queue::{DISCONNECT, Links};
use crate::solver::{Assigned, ELIMINATED, Frame, Solver};
use crate::types::{Lit, Var};
use crate::watch::{self, Watch};

const UNMAPPED: u32 = u32::MAX;

impl Solver {
    /// Compact if enough variables became inactive.  Must be called at the
    /// root level (outside of dense mode).
    pub(crate) fn compacting(&self) -> bool {
        if !self.opts.compact || self.level != 0 || self.dense || self.inconsistent {
            return false;
        }
        let fixed = self.trail.len();
        let inactive = self.eliminated as usize + fixed;
        inactive > 0 && inactive * 100 >= self.opts.compactlim as usize * self.vars
    }

    /// Returns false if the formula became inconsistent.
    pub(crate) fn compact(&mut self) -> bool {
        debug_assert_eq!(self.level, 0);
        // Export pending units and remove root-level literals from clauses.
        if self.sharing.pool.is_some() && !self.share_units() {
            return false;
        }
        // Repeat until propagation finds no new units (which would leave
        // root-level literals in clauses).
        loop {
            let before = self.trail.len();
            if !self.resync_watches() {
                return false;
            }
            if self.trail.len() == before {
                break;
            }
        }
        self.flush_pending_units();
        let old_vars = self.vars;
        let mut map = vec![UNMAPPED; old_vars];
        let mut new_i2e: Vec<u32> = Vec::new();
        for v in 0..old_vars {
            let e = self.ext.i2e[v] as usize;
            let value = self.values[2 * v];
            if self.flags[v].has(ELIMINATED) {
                self.ext.e2i[e] = Lit::INVALID;
            } else if value != 0 {
                self.ext.fixed[e] = value;
                self.ext.e2i[e] = Lit::INVALID;
            } else {
                map[v] = new_i2e.len() as u32;
                self.ext.e2i[e] = Lit::new(map[v], false);
                new_i2e.push(e as u32);
            }
        }
        let n = new_i2e.len();
        let map_lit = |l: Lit| -> Lit {
            let m = map[l.vidx()];
            debug_assert!(m != UNMAPPED, "literal of inactive variable {l}");
            Lit::new(m, l.negated())
        };

        // Clauses (the arena has no garbage after `resync_watches`).
        let mut c = 0;
        while (c as usize) < self.arena.len() {
            let size = self.arena.size(c);
            let base = c as usize + HEADER;
            for k in 0..size {
                let l = Lit(self.arena.mem[base + k]);
                self.arena.mem[base + k] = map_lit(l).0;
            }
            c = self.arena.next(c);
        }

        // Watches: binary clauses from the old lists, large ones re-watched.
        let mut watches: Vec<watch::WatchList> = vec![Vec::new(); 2 * n];
        for idx in 0..self.watches.len() {
            let lit = Lit(idx as u32);
            if map[lit.vidx()] == UNMAPPED {
                continue;
            }
            for w in watch::iter(&self.watches[idx]) {
                if let Watch::Binary(other) = w
                    && map[other.vidx()] != UNMAPPED
                {
                    watch::push_binary(&mut watches[map_lit(lit).idx()], map_lit(other));
                }
            }
        }
        self.watches = watches;
        let mut c = 0;
        while (c as usize) < self.arena.len() {
            self.watch_clause(c);
            c = self.arena.next(c);
        }

        // Per variable data.
        fn remap<T: Copy + Default>(old: &[T], map: &[u32], n: usize) -> Vec<T> {
            let mut new = vec![T::default(); n];
            for (v, &m) in map.iter().enumerate() {
                if m != UNMAPPED {
                    new[m as usize] = old[v];
                }
            }
            new
        }
        self.flags = remap(&self.flags, &map, n);
        self.factor_flags = remap(&self.factor_flags, &map, n);
        self.phases.saved = remap(&self.phases.saved, &map, n);
        self.phases.target = remap(&self.phases.target, &map, n);
        self.phases.best = remap(&self.phases.best, &map, n);
        self.assigned = vec![Assigned::default(); n];
        self.values = vec![0; 2 * n];
        self.marks = vec![0; 2 * n];

        // Scores and decision queue (keeping the order).
        let mut heap = Heap::default();
        heap.resize(n);
        for v in 0..old_vars {
            if map[v] != UNMAPPED {
                heap.score[map[v] as usize] = self.heap.score[v];
            }
        }
        for v in 0..n {
            heap.push(v as Var);
        }
        self.heap = heap;
        let mut order: Vec<Var> = Vec::with_capacity(n);
        let mut idx = self.queue.first;
        while idx != DISCONNECT {
            if map[idx as usize] != UNMAPPED {
                order.push(map[idx as usize]);
            }
            idx = self.queue.links[idx as usize].next;
        }
        self.queue.links = vec![Links::default(); n];
        self.queue.rebuild(&order);

        // Trail and search state (only root-level literals were assigned).
        self.trail.clear();
        self.propagated = 0;
        self.frames = vec![Frame::default()];
        self.level = 0;
        self.vars = n;
        self.unassigned = n as u32;
        self.eliminated = 0;
        self.sharing.exported = 0;
        self.ext.i2e = new_i2e;
        if let Some(p) = self.proof.as_mut() {
            p.map = self.ext.i2e.clone();
        }
        for l in self.last_learned.iter_mut() {
            *l = INVALID_REF;
        }
        self.seen.clear();
        self.first_seen.clear();
        self.recount_phase_heights();
        self.stats.compacts += 1;
        if self.verbose(2) {
            println!(
                "c [compact-{}] {} -> {} variables",
                self.stats.compacts, old_vars, n
            );
        }
        true
    }
}
