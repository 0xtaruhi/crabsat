#!/usr/bin/env python3
"""Run a SAT solver over a set of CNF instances in parallel and record results.

usage: bench.py --solver CMD --out results.csv [--timeout 60] [--jobs 16] FILES...

CMD is split on whitespace; the instance path is appended as the last argument.
The CSV contains: instance, status (SAT/UNSAT/UNKNOWN/ERROR), seconds.
"""
import argparse
import concurrent.futures as cf
import csv
import os
import subprocess
import sys
import time


def run_one(cmd, path, timeout):
    start = time.monotonic()
    try:
        proc = subprocess.run(cmd + [path], stdout=subprocess.PIPE,
                              stderr=subprocess.DEVNULL, timeout=timeout)
        elapsed = time.monotonic() - start
        code = proc.returncode
        status = {10: "SAT", 20: "UNSAT", 0: "UNKNOWN"}.get(code, "ERROR")
        if status == "ERROR":
            sys.stderr.write(f"error: exit code {code} on {path}\n")
    except subprocess.TimeoutExpired:
        elapsed, status = timeout, "UNKNOWN"
    return os.path.basename(path), status, elapsed


def summarize(rows, timeout):
    solved = [r for r in rows if r[1] in ("SAT", "UNSAT")]
    par2 = sum(r[2] if r[1] in ("SAT", "UNSAT") else 2 * timeout for r in rows)
    sat = sum(1 for r in rows if r[1] == "SAT")
    errors = sum(1 for r in rows if r[1] == "ERROR")
    print(f"solved {len(solved)}/{len(rows)} (SAT {sat}, UNSAT {len(solved) - sat})"
          f"  errors {errors}  PAR-2 {par2:.1f}"
          f"  time(solved) {sum(r[2] for r in solved):.1f}s")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--solver", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--timeout", type=float, default=60)
    ap.add_argument("--jobs", type=int, default=16)
    ap.add_argument("files", nargs="+")
    args = ap.parse_args()
    cmd = args.solver.split()
    rows = []
    with cf.ThreadPoolExecutor(args.jobs) as ex:
        futures = [ex.submit(run_one, cmd, f, args.timeout) for f in args.files]
        for fut in cf.as_completed(futures):
            rows.append(fut.result())
    rows.sort()
    with open(args.out, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["instance", "status", "seconds"])
        for r in rows:
            w.writerow([r[0], r[1], f"{r[2]:.3f}"])
    summarize(rows, args.timeout)


if __name__ == "__main__":
    main()
