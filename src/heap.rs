//! Binary max-heap over variables keyed by `f64` scores (Kissat `heap.c`).
//! Used for VSIDS-style decisions in stable mode.

use crate::types::Var;

const ABSENT: u32 = u32::MAX;

#[derive(Default, Clone)]
pub struct Heap {
    pub score: Vec<f64>,
    pos: Vec<u32>,
    heap: Vec<Var>,
}

impl Heap {
    pub fn resize(&mut self, vars: usize) {
        self.score.resize(vars, 0.0);
        self.pos.resize(vars, ABSENT);
    }

    #[inline]
    pub fn contains(&self, v: Var) -> bool {
        self.pos[v as usize] != ABSENT
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.heap.is_empty()
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.heap.len()
    }

    #[inline]
    pub fn max(&self) -> Var {
        self.heap[0]
    }

    #[inline]
    fn less(&self, a: Var, b: Var) -> bool {
        self.score[a as usize] < self.score[b as usize]
    }

    fn up(&mut self, v: Var) {
        let mut i = self.pos[v as usize] as usize;
        while i > 0 {
            let parent_i = (i - 1) / 2;
            let parent = self.heap[parent_i];
            if !self.less(parent, v) {
                break;
            }
            self.heap[i] = parent;
            self.pos[parent as usize] = i as u32;
            i = parent_i;
        }
        self.heap[i] = v;
        self.pos[v as usize] = i as u32;
    }

    fn down(&mut self, v: Var) {
        let n = self.heap.len();
        let mut i = self.pos[v as usize] as usize;
        loop {
            let mut child_i = 2 * i + 1;
            if child_i >= n {
                break;
            }
            let mut child = self.heap[child_i];
            if child_i + 1 < n {
                let right = self.heap[child_i + 1];
                if self.less(child, right) {
                    child_i += 1;
                    child = right;
                }
            }
            if !self.less(v, child) {
                break;
            }
            self.heap[i] = child;
            self.pos[child as usize] = i as u32;
            i = child_i;
        }
        self.heap[i] = v;
        self.pos[v as usize] = i as u32;
    }

    pub fn push(&mut self, v: Var) {
        debug_assert!(!self.contains(v));
        self.pos[v as usize] = self.heap.len() as u32;
        self.heap.push(v);
        self.up(v);
    }

    pub fn pop_max(&mut self) -> Var {
        let top = self.heap[0];
        let last = self.heap.pop().unwrap();
        self.pos[top as usize] = ABSENT;
        if top != last {
            self.pos[last as usize] = 0;
            self.heap[0] = last;
            self.down(last);
        }
        top
    }

    /// Set a new score, restoring the heap property if `v` is contained.
    pub fn update(&mut self, v: Var, new_score: f64) {
        let old = self.score[v as usize];
        self.score[v as usize] = new_score;
        if self.contains(v) {
            if new_score > old {
                self.up(v);
            } else if new_score < old {
                self.down(v);
            }
        }
    }

    pub fn max_score(&self) -> f64 {
        self.score.iter().copied().fold(0.0, f64::max)
    }

    pub fn rescale(&mut self, factor: f64) {
        for s in &mut self.score {
            *s *= factor;
        }
    }

    /// Remove all elements (keeps scores).
    pub fn clear(&mut self) {
        for &v in &self.heap {
            self.pos[v as usize] = ABSENT;
        }
        self.heap.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn heap_order() {
        let mut h = Heap::default();
        h.resize(10);
        for v in 0..10 {
            h.score[v] = ((v * 7) % 10) as f64;
            h.push(v as Var);
        }
        h.update(3, 100.0);
        assert_eq!(h.pop_max(), 3);
        let mut prev = f64::INFINITY;
        while !h.is_empty() {
            let v = h.pop_max();
            assert!(h.score[v as usize] <= prev);
            prev = h.score[v as usize];
        }
    }
}
