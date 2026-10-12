#!/usr/bin/env python3
"""Differential fuzzing: random CNFs, compare crabsat with a reference
solver, check models (--check) and verify UNSAT proofs with drat-trim.

usage: fuzz.py --crabsat BIN --ref KISSAT --drat-trim BIN [-n 1000] [--seed S]
               [--opts "--stable=2 ..."]
"""
import argparse
import os
import random
import subprocess
import sys
import tempfile


def structured_cnf(rng):
    # Pigeon-hole like: pigeons into holes with at-least-one and pairwise
    # at-most-one constraints, plus some random clauses.
    holes = rng.randint(2, 7)
    pigeons = holes + rng.choice([-1, 0, 1, 1])
    var = lambda p, h: p * holes + h + 1
    n = pigeons * holes
    clauses = [[var(p, h) for h in range(holes)] for p in range(pigeons)]
    for h in range(holes):
        for p in range(pigeons):
            for q in range(p + 1, pigeons):
                clauses.append([-var(p, h), -var(q, h)])
    for _ in range(rng.randint(0, n // 2)):
        clauses.append([rng.randint(1, n) * rng.choice([1, -1]) for _ in range(rng.randint(2, 4))])
    rng.shuffle(clauses)
    return n, clauses


def miter_cnf(rng):
    import subprocess
    here = os.path.dirname(os.path.abspath(__file__))
    args = [sys.executable, os.path.join(here, "gen_miter.py"),
            str(rng.randint(2, 10)), str(rng.randint(1, 40)), str(rng.randrange(1 << 30))]
    if rng.random() < 0.5:
        args.append("--sat")
    out = subprocess.run(args, stdout=subprocess.PIPE, check=True).stdout.decode().split("\n")
    n = int(out[0].split()[2])
    clauses = [list(map(int, l.split()))[:-1] for l in out[1:] if l.strip()]
    return n, clauses


def random_cnf(rng):
    kind = rng.random()
    if kind < 0.15:
        return miter_cnf(rng)
    if kind < 0.3:
        return structured_cnf(rng)
    if kind < 0.6:
        # Random k-SAT near the threshold.
        k = rng.choice([3, 3, 3, 4, 5])
        n = rng.randint(5, {3: 150, 4: 70, 5: 45}[k])
        ratio = {3: 4.26, 4: 9.93, 5: 21.1}[k] * rng.uniform(0.85, 1.15)
        m = int(n * ratio)
        clauses = [[v if rng.random() < 0.5 else -v
                    for v in rng.sample(range(1, n + 1), k)] for _ in range(m)]
    else:
        # Mixed clause lengths with units, binaries, duplicates, tautologies.
        n = rng.randint(1, 60)
        m = rng.randint(1, 6 * n)
        clauses = []
        for _ in range(m):
            size = rng.choice([1, 2, 2, 3, 3, 3, 4, 5, 8]) if rng.random() < 0.97 else 0
            clauses.append([rng.randint(1, n) * rng.choice([1, -1]) for _ in range(size)])
        if rng.random() < 0.1:
            clauses = [c for c in clauses if c]  # sometimes no empty clause
    return n, clauses


def write_cnf(path, n, clauses):
    with open(path, "w") as f:
        f.write(f"p cnf {n} {len(clauses)}\n")
        for c in clauses:
            f.write(" ".join(map(str, c)) + " 0\n")


def run(cmd, timeout=60):
    p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout)
    return p.returncode, p.stdout.decode(), p.stderr.decode()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--crabsat", required=True)
    ap.add_argument("--ref", required=True)
    ap.add_argument("--drat-trim", required=True)
    ap.add_argument("-n", type=int, default=1000)
    ap.add_argument("--seed", type=int, default=None)
    ap.add_argument("--opts", default="")
    args = ap.parse_args()
    seed = args.seed if args.seed is not None else random.randrange(1 << 30)
    print(f"seed {seed}")
    rng = random.Random(seed)
    tmp = tempfile.mkdtemp(prefix="crabsat-fuzz-")
    cnf, proof = os.path.join(tmp, "f.cnf"), os.path.join(tmp, "f.drat")
    counts = {10: 0, 20: 0}
    for i in range(args.n):
        n, clauses = random_cnf(rng)
        write_cnf(cnf, n, clauses)
        ref, _, _ = run([args.ref, "-q", "-n", cnf])
        with_proof = "--threads" not in args.opts
        files = [cnf, proof] if with_proof else [cnf]
        res, out, err = run([args.crabsat, "-q", "--check", *args.opts.split(), *files])
        if res != ref or res not in (10, 20):
            fail = os.path.join(os.getcwd(), f"fuzz-fail-{seed}-{i}.cnf")
            write_cnf(fail, n, clauses)
            print(f"MISMATCH on case {i}: crabsat {res} reference {ref} -> {fail}")
            print(out[-2000:], err[-2000:])
            sys.exit(1)
        if res == 20 and with_proof:
            code, dout, _ = run([args.drat_trim, cnf, proof, "-f"], timeout=300)
            if "s VERIFIED" not in dout:
                fail = os.path.join(os.getcwd(), f"fuzz-proof-{seed}-{i}.cnf")
                write_cnf(fail, n, clauses)
                print(f"PROOF FAILED on case {i} -> {fail}")
                print(dout[-2000:])
                sys.exit(1)
        counts[res] += 1
        if (i + 1) % 100 == 0:
            print(f"{i + 1} cases ok (SAT {counts[10]}, UNSAT {counts[20]})", flush=True)
    print(f"all {args.n} cases ok (SAT {counts[10]}, UNSAT {counts[20]})")


if __name__ == "__main__":
    main()
