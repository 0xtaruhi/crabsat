# Changelog

## 0.1.2 - 2026-10-15

- `Solver::set_conflict_limit` is exact: a call never counts more
  conflicts than its limit (the limit is checked after every conflict
  analysis, and on-the-fly strengthening stops at the limit), and a call
  stopped by the limit has counted exactly that many.

## 0.1.1 - 2026-10-14

- WebAssembly: the library no longer panics on `wasm32-unknown-unknown`
  (which has no clock); times in the statistics are zero there.  CI runs a
  smoke test of the library on that target with Node.js.
- `crabsat::VERSION`: the version of the crate.

## 0.1.0 - 2026-10-14

- First release: CDCL solver following Kissat with inprocessing, DRAT
  proofs, parallel portfolio, incremental API (assumptions, failed
  assumptions, callbacks, interrupts, limits, phases, freezing) and an
  IPASIR C library.
