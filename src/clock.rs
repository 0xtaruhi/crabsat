//! Wall-clock time for statistics and messages.  `wasm32-unknown-unknown`
//! has no clock (`std::time::Instant::now` panics there), so times are
//! reported as zero on that target; the search never depends on time.

#[cfg(not(all(target_family = "wasm", target_os = "unknown")))]
#[derive(Clone, Copy, Debug)]
pub(crate) struct Instant(std::time::Instant);

#[cfg(not(all(target_family = "wasm", target_os = "unknown")))]
impl Instant {
    pub(crate) fn now() -> Instant {
        Instant(std::time::Instant::now())
    }

    /// Seconds since `self`.
    pub(crate) fn seconds(&self) -> f64 {
        self.0.elapsed().as_secs_f64()
    }
}

#[cfg(all(target_family = "wasm", target_os = "unknown"))]
#[derive(Clone, Copy, Debug)]
pub(crate) struct Instant;

#[cfg(all(target_family = "wasm", target_os = "unknown"))]
impl Instant {
    pub(crate) fn now() -> Instant {
        Instant
    }

    pub(crate) fn seconds(&self) -> f64 {
        0.0
    }
}
