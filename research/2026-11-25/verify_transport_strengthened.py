#!/usr/bin/env python3
"""Exact finite checks of strengthened Q bounds and transport candidates.

For repeated colors f_h uses a STRICT prefix-min stopping indicator.  It is
the bucket-truncated representation of comparison cost, not the comparison
count of insertion sort applied directly to repeated labels.
"""

from fractions import Fraction
from itertools import combinations_with_replacement, permutations, product
from pathlib import Path
import json
import time

from verify_joint_framework import (all_contiguous_partitions, bucket_information,
                                    equal_buckets, selected_words)


HERE = Path(__file__).resolve().parent


def cost(z, h):
    total = 0
    for r in range(min(h, len(z))):
        chain = z[r::h]
        for j in range(1, len(chain)):
            total += sum(chain[i] > chain[j] for i in range(j))
            total += int(chain[j] > min(chain[:j]))
    return total


def sorted_pass(z, h):
    out = list(z)
    for r in range(min(h, len(z))):
        out[r::h] = sorted(z[r::h])
    return tuple(out)


def distance(z, w):
    return sum(abs(a - b) for a, b in zip(z, w))


def hamming(z, w):
    return sum(a != b for a, b in zip(z, w))


def lipschitz_neighbors():
    checks = 0
    equality_count = 0
    example = None
    per_n = []
    for n in range(1, 8):
        before = checks
        for z in product(range(3), repeat=n):
            for h in range(1, n + 1):
                bound = (n + h - 1) // h - 1
                fz = cost(z, h)
                for i in range(n):
                    for new in range(3):
                        if z[i] == new:
                            continue
                        w = z[:i] + (new,) + z[i + 1:]
                        delta = abs(fz - cost(w, h))
                        assert delta <= bound, ("one_coordinate_Lipschitz", z, w, h, delta, bound)
                        if bound and delta == bound:
                            equality_count += 1
                            if example is None or bound > example["bound"]:
                                example = {"z": z, "w": w, "h": h, "cost_difference": delta, "bound": bound}
                        checks += 1
        per_n.append({"n": n, "vectors": 3 ** n, "neighbor_checks": checks - before})
    return {"checks": checks, "per_n": per_n, "positive_bound_equalities": equality_count,
            "sharpness_witness": example}


def all_pair_transport():
    checks = 0
    per_n = []
    for n in range(1, 7):
        before = checks
        states = tuple(product(range(3), repeat=n))
        for h in range(1, n + 1):
            outputs = {z: sorted_pass(z, h) for z in states}
            costs = {z: cost(z, h) for z in states}
            L = (n + h - 1) // h - 1
            for z, w in combinations_with_replacement(states, 2):
                D = distance(z, w)
                assert distance(outputs[z], outputs[w]) <= D, ("sort_nonexpansion", n, h, z, w)
                assert abs(costs[z] - costs[w]) <= L * hamming(z, w), ("global_Hamming_Lipschitz", n, h, z, w)
                assert abs(costs[z] - costs[w]) <= L * D
                checks += 1
        per_n.append({"n": n, "vectors": len(states), "unordered_pair_gap_checks": checks - before})
    return {"checks": checks, "per_n": per_n}


def word_cost(z, word):
    out = z
    total = 0
    for h in word:
        total += cost(out, h)
        out = sorted_pass(out, h)
    return total


def word_transport():
    checks = 0
    word_records = []
    for n in range(2, 7):
        states = tuple(product(range(3), repeat=n))
        for word in selected_words(n):
            coefficient = sum((n + h - 1) // h - 1 for h in word)
            costs = {z: word_cost(z, word) for z in states}
            this_checks = 0
            for z, w in combinations_with_replacement(states, 2):
                assert abs(costs[z] - costs[w]) <= coefficient * distance(z, w), ("word_transport", n, word, z, w)
                checks += 1
                this_checks += 1
            word_records.append({"n": n, "word": word, "coefficient": coefficient, "coupled_pair_checks": this_checks})
    return {"checks": checks, "words": word_records}


def stronger_q_bounds():
    finite_checks = pi_checks = 0
    max_ratio = Fraction(0)
    ratio_witness = None
    for n in range(1, 8):
        partitions = tuple(all_contiguous_partitions(n)) if n <= 6 else tuple(dict.fromkeys(equal_buckets(n, b) for b in range(1, n + 1)))
        infos = [(boundaries,) + bucket_information(boundaries) for boundaries in partitions]
        rhs_factor = {(h, b): 2 * sum((Fraction(1, (k * h - b + 1) ** 2)
                                     for k in range(1, (n - 1) // h + 1)), Fraction(0))
                      for h in range(1, n + 1) for b in range(1, h + 1)}
        for x in permutations(range(n)):
            Q = sum((value - i) ** 2 for i, value in enumerate(x))
            for h in range(1, n + 1):
                position_pairs = tuple((i, j) for i in range(n) for j in range(i + h, n, h))
                for boundaries, ids, b, _ in infos:
                    if h < b:
                        continue
                    U = sum(ids[x[i]] == ids[x[j]] for i, j in position_pairs)
                    factor = rhs_factor[h, b]
                    assert U * factor.denominator <= Q * factor.numerator, ("stronger_finite_Q", n, x, h, boundaries, U, Q)
                    finite_checks += 1
                    if h >= 2 * b:
                        # Check the stronger constant 9, so pi > 3 implies the requested bound.
                        assert U * h * h <= 9 * Q, ("stronger_than_pi_squared_Q", n, x, h, boundaries, U, Q)
                        pi_checks += 1
                        if Q and Fraction(U * h * h, Q) > max_ratio:
                            max_ratio = Fraction(U * h * h, Q)
                            ratio_witness = {"n": n, "permutation": x, "h": h, "boundaries": boundaries, "U": U, "Q": Q}
    return {"finite_series_coefficient": 2, "finite_series_checks": finite_checks,
            "pi_squared_bound_checks": pi_checks, "actually_checked_constant": 9,
            "max_observed_Uh_squared_over_Q": str(max_ratio), "max_ratio_witness": ratio_witness}


def rejected_footrule_half_bound():
    """A targeted n=9 regression: the tempting half-size F bound is false."""
    x = (0, 3, 6, 1, 4, 7, 2, 5, 8)
    h = 3
    boundaries = (0, 3, 6, 9)
    ids, b, _ = bucket_information(boundaries)
    F = sum(abs(value - i) for i, value in enumerate(x))
    U = sum(ids[x[i]] == ids[x[j]] for i in range(len(x)) for j in range(i + h, len(x), h))
    original_rhs = 2 * F + len(x) * (b - 1)
    rejected_rhs = Fraction(original_rhs, 2)
    assert (U, F) == (9, 16)
    assert U * h <= original_rhs
    assert U * h > rejected_rhs
    return {"permutation": x, "n": len(x), "gap": h, "bucket_boundaries": boundaries,
            "U": U, "F": F, "U_times_h": U * h, "original_rhs": original_rhs,
            "rejected_half_rhs": str(rejected_rhs),
            "interpretation": "U*h <= F+n*(b-1)/2 is false; all small-n passes do not justify this strengthening"}


def main():
    start = time.perf_counter()
    result = {"status": "running", "arithmetic": "exact integers and rational numbers",
              "cost_definition": "chain inversions plus STRICT current-color > prefix-min-color indicators",
              "scope": "Finite verification only; no Lean formalization and no proof for all n."}
    for name, operation in (("one_coordinate_lipschitz", lipschitz_neighbors),
                            ("all_pair_transport", all_pair_transport),
                            ("word_transport", word_transport),
                            ("strengthened_q", stronger_q_bounds),
                            ("rejected_F_half_bound", rejected_footrule_half_bound)):
        before = time.perf_counter()
        result[name] = operation()
        result[name + "_seconds"] = round(time.perf_counter() - before, 6)
        print(f"PASS {name}: {result[name + '_seconds']:.3f}s", flush=True)
    result["status"] = "passed"
    result["total_seconds"] = round(time.perf_counter() - start, 6)
    (HERE / "transport_strengthened_results.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {HERE / 'transport_strengthened_results.json'}", flush=True)


if __name__ == "__main__":
    main()
