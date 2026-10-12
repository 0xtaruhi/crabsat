#!/usr/bin/env python3
"""Generate a miter CNF: two structurally identical random circuits (AND,
ITE and XOR gates, Tseitin encoded with fresh variables) on the same inputs
whose outputs are asserted to differ.  The result is unsatisfiable, and
congruence closure proves it without search.

usage: gen_miter.py INPUTS GATES SEED [--sat]
With --sat one gate of the second copy is changed (usually satisfiable).
"""
import random
import sys


def main():
    inputs, gates, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    sat = "--sat" in sys.argv
    rng = random.Random(seed)
    clauses = []
    nvars = inputs

    def fresh():
        nonlocal nvars
        nvars += 1
        return nvars

    def and_gate(a, b):
        x = fresh()
        clauses.extend([[-x, a], [-x, b], [x, -a, -b]])
        return x

    def xor_gate(a, b):
        x = fresh()
        clauses.extend([[-x, a, b], [-x, -a, -b], [x, -a, b], [x, a, -b]])
        return x

    def ite_gate(c, t, e):
        x = fresh()
        clauses.extend([[-c, -t, x], [-c, t, -x], [c, -e, x], [c, e, -x]])
        return x

    structure = []
    for i in range(gates):
        kind = rng.choice(["and", "and", "xor", "ite"])
        args = [rng.randrange(inputs + i) for _ in range(3)]
        signs = [rng.choice([1, -1]) for _ in range(3)]
        structure.append((kind, args, signs))
    mutate = rng.randrange(gates) if sat else -1

    def build(copy):
        nodes = list(range(1, inputs + 1))
        for i, (kind, args, signs) in enumerate(structure):
            lits = [signs[k] * nodes[args[k]] for k in range(3)]
            if copy == 1 and i == mutate:
                lits[0] = -lits[0]
            if kind == "and":
                nodes.append(and_gate(lits[0], lits[1]))
            elif kind == "xor":
                nodes.append(xor_gate(lits[0], lits[1]))
            else:
                nodes.append(ite_gate(lits[0], lits[1], lits[2]))
        return nodes[-1]

    o1, o2 = build(0), build(1)
    # Assert o1 != o2.
    clauses.extend([[o1, o2], [-o1, -o2]])
    print(f"p cnf {nvars} {len(clauses)}")
    for c in clauses:
        print(" ".join(map(str, c)) + " 0")


if __name__ == "__main__":
    main()
