#!/usr/bin/env python3
"""Dependency-free, exhaustive finite oracle for binary HGP erasures.

Run `python3 supervision/oracle.py` from the experiment directory.  This checks
every binary matrix with 0 <= rows, columns <= 2, every ordered pair, and every
erasure subset of its HGP qubits (at most eight).  Dimensions are stored even
when a matrix has no rows or columns.  The brute-force path enumerates actual
words and stabilizer cosets; it does not call the rank-formula implementation.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from itertools import product
import json
from pathlib import Path


@dataclass(frozen=True)
class Matrix:
    ncols: int
    rows: tuple[int, ...]

    def __post_init__(self):
        if self.ncols < 0 or any(r < 0 or r >= 1 << self.ncols for r in self.rows):
            raise ValueError("row outside declared column dimension")

    @property
    def nrows(self):
        return len(self.rows)

    def transpose(self):
        return Matrix(self.nrows, tuple(
            sum(((r >> j) & 1) << i for i, r in enumerate(self.rows))
            for j in range(self.ncols)))

    def restrict(self, mask):
        # Zero columns do not affect rank; preserve positions for simplicity.
        return Matrix(self.ncols, tuple(r & mask for r in self.rows))


def rank(a):
    pivots = {}
    for row in a.rows:
        while row:
            p = row.bit_length() - 1
            if p in pivots:
                row ^= pivots[p]
            else:
                pivots[p] = row
                break
    return len(pivots)


def kron(a, b):
    return Matrix(a.ncols * b.ncols, tuple(
        sum(br << (j * b.ncols) for j in range(a.ncols) if ar >> j & 1)
        for ar in a.rows for br in b.rows))


def eye(n):
    return Matrix(n, tuple(1 << j for j in range(n)))


def horizontal(a, b):
    if a.nrows != b.nrows:
        raise ValueError("incompatible row counts")
    return Matrix(a.ncols + b.ncols,
                  tuple(x | (y << a.ncols) for x, y in zip(a.rows, b.rows)))


def hgp(h1, h2):
    """Hx=[H1 tensor I_n2 | I_m1 tensor H2^T], similarly Hz."""
    hx = horizontal(kron(h1, eye(h2.ncols)), kron(eye(h1.nrows), h2.transpose()))
    hz = horizontal(kron(eye(h1.ncols), h2), kron(h1.transpose(), eye(h2.nrows)))
    return hx, hz


def syndrome(a, word):
    return sum(((r & word).bit_count() & 1) << j for j, r in enumerate(a.rows))


def rowspace(a):
    # Enumerating all row combinations is deliberately independent of rank().
    words = {0}
    for row in a.rows:
        words |= {w ^ row for w in words}
    return words


def submasks(mask):
    word = mask
    while True:
        yield word
        if word == 0:
            break
        word = (word - 1) & mask


def power_two_log(size):
    if size == 0 or size & (size - 1):
        raise AssertionError(f"not a binary vector-space cardinality: {size}")
    return size.bit_length() - 1


class WordQuotient:
    """Actual words modulo enumerated stabilizer words, with no rank calls."""

    def __init__(self, checks, stabilizers):
        self.n = checks.ncols
        self.checks = checks
        self.stabilizers = rowspace(stabilizers)
        assert all(syndrome(checks, s) == 0 for s in self.stabilizers)
        self.coset = {}
        for word in range(1 << self.n):
            if word not in self.coset:
                coset_words = {word ^ s for s in self.stabilizers}
                representative = min(coset_words)
                for member in coset_words:
                    self.coset[member] = representative
        self.cycles = tuple(w for w in range(1 << self.n) if syndrome(checks, w) == 0)
        self.syndromes = tuple(syndrome(checks, w) for w in range(1 << self.n))

    def ell(self, erased):
        classes = {self.coset[w] for w in self.cycles if w & ~erased == 0}
        return power_two_log(len(classes))

    def unique_same_syndrome(self, erased):
        """Every pair of errors in E sharing syndrome has equal logical coset."""
        seen = {}
        for word in submasks(erased):
            syn, coset = self.syndromes[word], self.coset[word]
            if syn in seen and seen[syn] != coset:
                return False
            seen[syn] = coset
        return True

    def distance(self):
        return min((w.bit_count() for w in self.cycles if self.coset[w] != 0),
                   default=None)


def formula(checks, stabilizers, erased):
    full = (1 << checks.ncols) - 1
    return (erased.bit_count() - rank(checks.restrict(erased))
            - rank(stabilizers) + rank(stabilizers.restrict(full ^ erased)))


def matrices(max_dimension=2):
    for m, n in product(range(max_dimension + 1), repeat=2):
        for rows in product(range(1 << n), repeat=m):
            yield Matrix(n, rows)


def validate_pair(h1, h2, counters):
    hx, hz = hgp(h1, h2)
    n, full = hx.ncols, (1 << hx.ncols) - 1
    assert n == h1.ncols * h2.ncols + h1.nrows * h2.nrows
    assert all((x & z).bit_count() % 2 == 0 for x in hx.rows for z in hz.rows)
    z, x = WordQuotient(hx, hz), WordQuotient(hz, hx)
    k = n - rank(hx) - rank(hz)
    assert k == z.ell(full) == x.ell(full)
    assert k == ((h1.ncols - rank(h1)) * (h2.ncols - rank(h2))
                 + (h1.nrows - rank(h1)) * (h2.nrows - rank(h2)))
    ells = [(z.ell(e), x.ell(e)) for e in range(1 << n)]
    for e, (ell_z, ell_x) in enumerate(ells):
        assert ell_z == formula(hx, hz, e), (h1, h2, e, "Z")
        assert ell_x == formula(hz, hx, e), (h1, h2, e, "X")
        assert ell_z + ells[full ^ e][1] == k
        assert ell_x + ells[full ^ e][0] == k
        assert z.unique_same_syndrome(e) == (ell_z == 0)
        assert x.unique_same_syndrome(e) == (ell_x == 0)
        counters["erasure_subsets"] += 1
        counters["rank_formula_comparisons"] += 2
        counters["cleaning_comparisons"] += 2
        counters["syndrome_uniqueness_comparisons"] += 2

    # Directly enumerate classical kernel words, independently of classical rank.
    ker1 = tuple(w for w in range(1 << h1.ncols) if syndrome(h1, w) == 0)
    ker2 = tuple(w for w in range(1 << h2.ncols) if syndrome(h2, w) == 0)
    k2 = power_two_log(len(ker2))
    for s in range(1 << h1.ncols):
        erased = sum(((1 << h2.ncols) - 1) << (i * h2.ncols)
                     for i in range(h1.ncols) if s >> i & 1)
        shortened = power_two_log(sum(w & ~s == 0 for w in ker1))
        projected = power_two_log(len({w & s for w in ker1}))
        assert ells[erased] == (shortened * k2, projected * k2), (h1, h2, s)
        counters["strip_subsets"] += 1
        counters["strip_formula_comparisons"] += 2
    counters["matrix_pairs"] += 1
    counters["zero_dimension_pairs"] += int(0 in (h1.nrows, h1.ncols, h2.nrows, h2.ncols))
    counters["redundant_row_pairs"] += int(rank(h1) < h1.nrows or rank(h2) < h2.nrows)
    return {"n": n, "k": k, "d_X": x.distance(), "d_Z": z.distance()}


def run():
    inputs = tuple(matrices())
    counters = dict.fromkeys(("matrix_pairs", "erasure_subsets", "rank_formula_comparisons",
                             "cleaning_comparisons", "syndrome_uniqueness_comparisons",
                             "strip_subsets", "strip_formula_comparisons", "zero_dimension_pairs",
                             "redundant_row_pairs"), 0)
    for h1, h2 in product(inputs, repeat=2):
        validate_pair(h1, h2, counters)
    examples = {}
    for name, h, expected in (("single_parity", Matrix(2, (3,)), (5, 1, 2)),
                              ("redundant_parity", Matrix(2, (3, 3)), (8, 2, 2))):
        ignored = dict.fromkeys(counters, 0)
        actual = validate_pair(h, h, ignored)
        assert (actual["n"], actual["k"], actual["d_X"]) == expected
        assert actual["d_Z"] == expected[2]
        # S = {0}: both examples have zero Z logicals and one X logical.
        hx, hz = hgp(h, h)
        actual["first_row_strip"] = {"ell_Z": WordQuotient(hx, hz).ell(3),
                                      "ell_X": WordQuotient(hz, hx).ell(3)}
        assert actual["first_row_strip"] == {"ell_Z": 0, "ell_X": 1}
        examples[name] = actual
    return {"status": "passed", "field": "GF(2)", "max_input_rows": 2,
            "max_input_columns": 2, "input_matrices": len(inputs),
            "max_physical_qubits": 8, "counts": counters, "examples": examples,
            "independence": "Actual words and enumerated stabilizer cosets versus Gaussian-elimination rank formulas"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path, help="also write the deterministic report to this path")
    args = parser.parse_args()
    report = json.dumps(run(), indent=2, sort_keys=True) + "\n"
    print(report, end="")
    if args.json:
        args.json.write_text(report)


if __name__ == "__main__":
    main()
