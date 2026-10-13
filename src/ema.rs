//! Bias-corrected exponential moving averages (Kissat `smooth.c`) and
//! reluctant doubling (Kissat `reluctant.c`).

#[derive(Clone, Copy, Debug, Default)]
pub struct Ema {
    pub value: f64,
    biased: f64,
    alpha: f64,
    beta: f64,
    exp: f64,
}

impl Ema {
    pub fn new(window: f64) -> Ema {
        let alpha = 1.0 / window;
        Ema {
            value: 0.0,
            biased: 0.0,
            alpha,
            beta: 1.0 - alpha,
            exp: 1.0,
        }
    }

    #[inline]
    pub fn update(&mut self, y: f64) {
        self.biased += self.alpha * (y - self.biased);
        if self.exp != 0.0 {
            let new_exp = self.exp * self.beta;
            if new_exp == self.exp {
                self.exp = 0.0;
                self.value = self.biased;
            } else {
                self.exp = new_exp;
                self.value = self.biased / (1.0 - new_exp);
            }
        } else {
            self.value = self.biased;
        }
    }
}

/// Averages kept separately for stable and focused mode.
#[derive(Clone, Copy, Debug, Default)]
pub struct Averages {
    pub initialized: bool,
    pub fast_glue: Ema,
    pub slow_glue: Ema,
    pub decision_rate: Ema,
    pub saved_decisions: u64,
}

impl Averages {
    pub fn init(&mut self, fast: f64, slow: f64) {
        if self.initialized {
            return;
        }
        self.initialized = true;
        self.fast_glue = Ema::new(fast);
        self.slow_glue = Ema::new(slow);
        self.decision_rate = Ema::new(slow);
    }
}

/// Luby-style reluctant doubling restart trigger (Knuth's formulation).
#[derive(Clone, Copy, Debug, Default)]
pub struct Reluctant {
    pub limited: bool,
    pub trigger: bool,
    pub period: u64,
    pub wait: u64,
    pub u: u64,
    pub v: u64,
    pub limit: u64,
}

impl Reluctant {
    pub fn enable(&mut self, mut period: u64, limit: u64) {
        if limit != 0 && period > limit {
            period = limit;
        }
        *self = Reluctant {
            limited: limit > 0,
            trigger: false,
            period,
            wait: period,
            u: 1,
            v: 1,
            limit,
        };
    }

    pub fn disable(&mut self) {
        self.period = 0;
    }

    #[inline]
    pub fn tick(&mut self) {
        if self.period == 0 || self.trigger {
            return;
        }
        self.wait -= 1;
        if self.wait != 0 {
            return;
        }
        let (mut u, mut v) = (self.u, self.v);
        if u.isolate_lowest_one() == v {
            u += 1;
            v = 1;
        } else {
            v *= 2;
        }
        let mut wait = v * self.period;
        if self.limited && wait > self.limit {
            u = 1;
            v = 1;
            wait = self.period;
        }
        self.trigger = true;
        self.wait = wait;
        self.u = u;
        self.v = v;
    }

    #[inline]
    pub fn triggered(&mut self) -> bool {
        let res = self.trigger;
        self.trigger = false;
        res
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn luby_sequence() {
        let mut r = Reluctant::default();
        r.enable(1, 0);
        let mut seq = Vec::new();
        let mut count = 0;
        while seq.len() < 15 {
            r.tick();
            count += 1;
            if r.triggered() {
                seq.push(count);
                count = 0;
            }
        }
        assert_eq!(seq, vec![1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8]);
    }

    #[test]
    fn ema_bias_correction() {
        let mut e = Ema::new(100.0);
        e.update(5.0);
        assert!((e.value - 5.0).abs() < 1e-9);
        for _ in 0..1000 {
            e.update(3.0);
        }
        assert!((e.value - 3.0).abs() < 1e-3);
    }
}
