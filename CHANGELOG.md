# Changelog

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
