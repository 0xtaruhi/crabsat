# crabsat roadmap

A high-performance CDCL SAT solver in Rust following the design of Kissat
(v4.0.4, MIT).

## Design principles

1. **Memory layout first** — clause arena with u32 offset references, binary
   clauses only in watch lists, literal-indexed value arrays, compact watches.
   The parts that are hard to change later are fixed first.
2. **Always verifiable** — DRAT proofs in every phase; models are checked and
   UNSAT proofs are verified with drat-trim.  Kissat serves as the oracle for
   differential testing.
3. **Budgets in ticks** — the search counts memory accesses in cache lines
   (ticks); mode switching and inprocessing budgets are proportional to them.
4. **Local unsafe** — bounds check elimination only in propagation, analysis
   and the arena, always guarded by `debug_assert!`.

## Milestones

Each milestone moves on once its definition of done (DoD) is met.

### M0: Foundation

- [x] Cargo project, release profile (lto=fat, codegen-units=1, panic=abort)
- [x] Types: `Lit`, `Var`, `CRef`, `Value` (i8)
- [x] DIMACS parser (xz/gz/bz2 decompressed with external tools)
- [x] SAT competition output (`s SATISFIABLE` / `v ...` / exit codes 10/20)
- [x] DRAT proof output (text / binary)
- [x] Test infrastructure (`scripts/fuzz.py`, `tests/basic.rs`): random CNF
  generation, model checking, drat-trim integration, differential testing
  against Kissat

### M1: CDCL core (MiniSat level)

- [x] Clause arena: header (glue, used, flags, searched, size) + literals
- [x] Binary clauses only in watch lists (virtual binaries)
- [x] Watches: Kissat's 32-bit variable length format (binary 1 word / large
  2 words)
- [x] Propagation as in Kissat (`lits[0]^lits[1]^not_lit`, searched position,
  delayed watches)
- [x] 1UIP analysis, recursive minimization (poison/removable)
- [x] VSIDS (binary heap, f64 scores, rescaling)
- [x] Learned clause reduction (glue + used)
- [x] Restarts (glue EMA), phase saving
- **DoD**: agreement with Kissat on random 3-SAT and 10k fuzz cases, all UNSAT
  proofs verified

### M2: Kissat search core

- [x] VMTF queue (focused mode), enqueue stamps, bumping sorted by stamp
- [x] Stable/focused mode switching (focused: conflicts, stable: ticks,
  n log⁴ n intervals)
- [x] Focused restarts: fast/slow glue EMA (bias corrected) with margin
- [x] Stable restarts: reluctant doubling (Luby)
- [x] Target / best phases, rephasing (best / walk / inverted / original)
- [x] Chronological backtracking (chronolevels=100)
- [x] Shrinking (Kissat's block-wise all-UIP shrinking, shrink=3)
- [x] Reason-side bumping (limited by decision rate)
- [x] Dynamic tier1/tier2 limits and reduction (used counters,
  reducehigh/low)
- [x] OTFS (on-the-fly strengthening)
- [x] Eager subsumption
- [x] Trail reuse on restarts
- [x] Statistics output (`c` lines)
- **DoD**: PAR-2 comparable to Kissat without inprocessing
  (`--simplify=false` etc.) on a SAT Competition 2023 subset

### M3: Basic inprocessing

- [x] Tick based scheduling (effort per mille, mineffort)
- [x] Garbage collection (arena compaction)
- [x] Compact (variable renumbering with external/internal maps)
- [x] Probing: failed literals (roots of the binary implication graph)
- [x] Substitute: equivalent literal substitution via SCCs of binary clauses
- [x] Transitive reduction
- [x] Vivification (tier1/tier2/tier3/irredundant)
- [x] Subsumption / strengthening (forward, one-watch)
- [x] BVE: bounded variable elimination with gate detection (AND / equivalence
  / ITE; XOR disabled by default)
- [x] Model reconstruction (extension stack)
- [ ] Binary clause backbone
- **DoD**: about 70–80% of the instances solved by default Kissat

### M4: Advanced techniques

- [x] Rephasing with local search (ProbSAT walk)
- [x] Lucky phases (before and after preprocessing), warmup
- [x] Kitten (embedded mini solver) and SAT sweeping (backbone and
  equivalences by partition refinement)
- [ ] Definition extraction with kitten (BVE)
- [x] Congruence closure (AND / ITE / XOR with RUP proofs, binary clause
  extraction, units from binary clause pairs)
- [x] Factor (bounded variable addition)
- [x] xz/gz compressed input
- [x] Decision reordering (reorder), random decision sequences (randec)

### M5: Beyond Kissat

- [x] IPASIR compatible incremental API (assumptions)
- [x] Parallel portfolio (`--threads=N`, sharing of root-level units)
- [x] Extended clause sharing (binary clauses, low glue learned clauses)

## Benchmarking

- Instances: SAT Competition 2023 main track (364 instances below 20 MB
  compressed).
- `scripts/bench.py` runs a solver on a set of instances in parallel and
  reports solved instances, PAR-2 and total time.
- Current reference set ("union"): the 162 instances solved by crabsat or
  Kissat within 120 s, run with a 60 s limit.  Solvers that are compared are
  run **simultaneously under the same load**, since SAT results vary strongly
  between runs and measurements taken at different times are not comparable.

## Development log

Initial benchmark: the 71 instances of the SAT Competition 2023 main track
which Kissat 4.0.4 solves in 1–30 s (`medium`, 37 SAT / 34 UNSAT), 120 s time
limit, 32 jobs in parallel.  PAR-2 counts unsolved instances as 240 s.

| version | solved | UNSAT PAR-2 | SAT PAR-2 | main additions |
|---|---|---|---|---|
| Kissat 4.0.4 (default) | 71/71 | 258 | 385 | — |
| Kissat (`--simplify=false --lucky=false --preprocess=false`) | 43/71 | 5011 | 2440 | — |
| M1/M2 (no inprocessing) | 40/71 | 5256 | 3188 | CDCL core + Kissat search heuristics |
| + BVE / subsumption | 43/71 | 5085 | 2737 | variable elimination, gates (AND/equivalence) |
| + probing | 46/71 | 4978 | 1910 | ELS substitution, failed literals, vivification |
| + factor | 67/71 | 292 | 1919 | bounded variable addition |
| + congruence / walk | 66/71 | 378 | 2018 | congruence closure, ProbSAT |
| + lucky / reorder / randec | 70/71 | 314 | 1193 | |
| + sweep / stronger vivify / factor fix / warmup | 69/71 | 289 | ~1450 | SAT results vary strongly between runs |

On all 364 instances (120 s): crabsat 138 / Kissat 137 solved (117 in common,
no SAT/UNSAT disagreement).

Note: this `medium` set was later found to be biased towards Kissat, since it
was selected from instances Kissat solved quickly with its default seed; with
other seeds Kissat fails on some of them as well.

Verification: at every step `scripts/fuzz.py` (random k-SAT, at-most-one
structures, miter circuits) was run on thousands of cases with various
options, checking agreement with Kissat, models (`--check`) and DRAT proofs
(drat-trim).

### 2026-10-13: Fixed invalid SAT answers in the portfolio

When a reason clause strengthened on the fly subsumed the conflict clause, the
conflict clause was deleted; if the conflict was irredundant and the reason
redundant, an irredundant clause was lost (Kissat promotes the reason to
irredundant).  Later model reconstruction after variable elimination depended
on the lost clause and produced invalid models.  The bug could also occur in
single-threaded mode but became frequent when unit sharing changed the search
path.  Found with import logging and replay (`CRABSAT_IMPORT_LOG` /
`CRABSAT_REPLAY`) and clause tracing (`CRABSAT_TRACE`).

| version | solved | UNSAT PAR-2 | SAT PAR-2 |
|---|---|---|---|
| after the fix, single thread | 65/71 | 407 | 2543 |
| after the fix, 8 threads | 70/71 | 338 | 958 |

(XOR gates in BVE are disabled by default since removing them improved the
UNSAT PAR-2 on the 34 UNSAT instances from 391 to 297.)

### 2026-10-13: On par with Kissat

New evaluation: the "union" set described above, run simultaneously with
Kissat.

Main improvements:
- Binary clause extraction before congruence closure (ternary clause + binary
  clause → binary clause)
- Units in congruence closure: `(l | o)` and `(l | !o)` imply `l` (large
  effect on big industrial instances after factorization)
- Compact (variable renumbering, separate external/internal numbering)
- Delays for unproductive simplifications (congruence / sweeping /
  irredundant vivification), minimum factorization reduction of 3
- Faster congruence (FxHash, canonical ITE gates, XOR grouping by sorting)

| union, 162 instances / 60 s | solved | SAT | UNSAT | PAR-2 |
|---|---|---|---|---|
| crabsat (run 1) | 94 | 46 | 48 | 9404 |
| Kissat 4.0.4 (run 1) | 91 | 48 | 43 | 9775 |
| crabsat (run 2) | 93 | 45 | 48 | 9477 |
| Kissat 4.0.4 (run 2) | 93 | 48 | 45 | 9625 |

Better on UNSAT, still 2–3 SAT instances behind at this point.

Closing the SAT gap: with three seeds per solver on the SAT instances both
solvers were already close on average (Kissat 37.7 vs crabsat 36.3 solved,
total time 8624 s vs 8651 s).  The consistent difference came from tiny
instances which Kissat solves with lucky assignments before preprocessing.
crabsat now tries lucky assignments before preprocessing as well and restores
the complete search state if they fail (propagation otherwise moves watches
and perturbs the later search).

### 2026-10-13: Multi-core (portfolio)

- Learned clause sharing: binary clauses and learned clauses with glue <= 2
  and size <= 8 over original variables are exchanged during restarts every
  500 conflicts and imported at the root level (clauses with eliminated
  variables are skipped).
- New diversification (always stable / negative phase / target phases in
  focused mode / stable with negative phase / stronger walk / without random
  decisions and reordering / focused only).
- Cloning a single preprocessed solver for all members was tried but was
  worse than letting every member preprocess with its own options in parallel
  (124 vs 126 solved), so it is not used.

| union, 162 instances / 60 s | solved | SAT | UNSAT | PAR-2 |
|---|---|---|---|---|
| Kissat 4.0.4 (single thread) | 92 | 49 | 43 | 9632 |
| crabsat single thread | 97 | 49 | 48 | 9258 |
| crabsat 4 threads | 121 | 71 | 50 | 6734 |
| crabsat 8 threads (unit sharing only, old diversification) | 116 | 65 | 51 | 7143 |
| crabsat 8 threads (clause sharing, new diversification) | 125 | 72 | 53 | 6290 |
| crabsat 16 threads | 126 | 72 | 54 | 6048 |

(Rows were measured under different machine loads; only rows measured
simultaneously are directly comparable.)

### 2026-10-13: Incremental API (IPASIR)

- `Solver::assume` / `failed` / `val` and the IPASIR C functions
  (`crabsat-ipasir` crate, `libcrabsat_ipasir.a` / `.so`,
  `include/ipasir.h`), with terminate and learn callbacks.
- Assumptions are decided first, one per decision level; assumptions that are
  already true get a decision level without assignment.  A falsified
  assumption is analyzed back through the reasons to the assumptions it
  depends on (failed assumptions).  Restarts keep the assumption levels.
- Variables of assumptions are frozen during a call (no elimination, no
  substitution).  In incremental mode, elimination saves all removed clauses
  on the extension stack (not only the witness unit for the negative side)
  and factor is disabled.  When a new clause or assumption mentions an
  eliminated or substituted variable, its saved clauses are added back
  transitively and the variable becomes active again (as in CaDiCaL).
- Tests: random sequences of clause additions, assumptions and solve calls
  checked against fresh solvers (results, models, failed assumptions as
  unsatisfiable cores), also with aggressive elimination and compaction.
