# crabsat

A high-performance CDCL SAT solver written in Rust, following the design of
[Kissat](https://github.com/arminbiere/kissat).

## Features

- **CDCL core** with Kissat's memory layout: clause arena with 32-bit
  references, binary clauses kept only in watch lists, compact watches with
  blocking literals.
- **Search heuristics**: alternating stable (VSIDS, reluctant doubling) and
  focused (VMTF, glue EMA restarts) modes, target/best phases, rephasing with
  local search (ProbSAT), chronological backtracking, shrinking, on-the-fly
  strengthening, tiered clause reduction.
- **Inprocessing**: bounded variable elimination with gate detection,
  subsumption, equivalent literal substitution, failed literals, transitive
  reduction, vivification, SAT sweeping with an embedded mini solver,
  congruence closure, bounded variable addition (factor), compaction.
- **DRAT proofs** (binary or text) for unsatisfiable formulas.
- **Parallel portfolio** (`--threads=N`) with diversified solvers sharing
  units and short low-glue learned clauses.
- **Incremental solving** through the [IPASIR](https://github.com/biotomas/ipasir)
  C interface and a Rust API (assumptions, failed assumptions, clauses added
  between calls, terminate and learn callbacks).

## Building

```sh
cargo build --release
```

## Usage

```sh
target/release/crabsat [options] <input.cnf[.xz|.gz|.bz2]> [<proof.drat>]
```

Compressed inputs (gzip, bzip2, xz, lzma) are decoded in-process with pure
Rust decoders (cargo feature `compression`, enabled by default), so no
external tools are needed on Linux, macOS or Windows.

The output follows the SAT competition format (`s SATISFIABLE` /
`s UNSATISFIABLE` with exit codes 10 / 20).  Useful options:

| option | description |
|---|---|
| `--threads=N` | run a portfolio of `N` solvers |
| `--time=S` | time limit in seconds |
| `--no-binary` | write the proof in text DRAT format |
| `--check` | check the model against the input formula |
| `-q`, `-v` | quiet / more verbose output |

`crabsat --help` lists all solver options.

## Performance

On SAT Competition 2023 main track instances (162 instances solved by either
crabsat or Kissat 4.0.4 within 120 s, 60 s time limit, same machine load):

| solver | solved | SAT | UNSAT | PAR-2 |
|---|---|---|---|---|
| Kissat 4.0.4 | 92 | 49 | 43 | 9632 |
| crabsat | 97 | 49 | 48 | 9258 |
| crabsat `--threads=8` | 125 | 72 | 53 | 6290 |

See [ROADMAP.md](ROADMAP.md) for the roadmap and development log.

## Incremental API

Rust:

```rust
use crabsat::{Options, SolveResult, Solver};

let mut s = Solver::new(Options { incremental: true, ..Options::default() });
s.add_clause(&[1, 2]);
s.add_clause(&[-1, 2]);
assert_eq!(s.solve(), SolveResult::Sat);
assert_eq!(s.val(2), 2);
s.assume(-2);
assert_eq!(s.solve(), SolveResult::Unsat);
assert!(s.failed(-2));
```

C (IPASIR, header [`include/ipasir.h`](include/ipasir.h)):

```sh
cargo build --release -p crabsat-ipasir
cc -Iinclude examples/ipasir_example.c target/release/libcrabsat_ipasir.a \
    -lpthread -ldl -lm -o example
```

This links the static library on Linux; the shared library
(`libcrabsat_ipasir.so` / `.dylib`, `crabsat_ipasir.dll`) is built as well,
and `cargo rustc --release -p crabsat-ipasir --crate-type staticlib --
--print native-static-libs` prints the system libraries needed for static
linking on other platforms.  CI builds and runs the example on Linux, macOS
and Windows.  All inprocessing
stays enabled in incremental mode except bounded variable addition: variables
of assumptions are frozen during a call, and variables removed by elimination
or substitution are reactivated (with their saved clauses) when later clauses
or assumptions mention them.

## Testing

```sh
cargo test --release
# longer randomized tests of the incremental API
CRABSAT_INCREMENTAL_RUNS=20000 cargo test --release --test incremental
# differential fuzzing against Kissat with model and DRAT proof checking
python3 scripts/fuzz.py --crabsat target/release/crabsat \
    --ref /path/to/kissat --drat-trim /path/to/drat-trim -n 1000
```

## License

MIT, see [LICENSE](LICENSE).  crabsat is inspired by Kissat; see
[THIRD_PARTY_NOTICES](THIRD_PARTY_NOTICES).
