#!/usr/bin/env python3
"""Independent finite checks for the Project S P02--P03 joint framework.

All arithmetic in reported theorem checks and means is exact.  These finite
checks are evidence about the implementation, not substitutes for general
proofs.  Ranks are 0,...,n-1.  A pass is ordinary, unguarded-by-sentinel chain
insertion; key comparisons only, including its final unsuccessful comparison.
"""

from collections import Counter, defaultdict
from fractions import Fraction
from itertools import permutations
from math import comb, factorial
from pathlib import Path
import json
import time


HERE = Path(__file__).resolve().parent


def frac_text(value):
    value = Fraction(value)
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def chain_lengths(n, h):
    return [len(range(r, n, h)) for r in range(min(h, n))]


def insertion_pass(x, h):
    """Direct algorithm, without consulting pair identities or bucket data."""
    y = list(x)
    comparisons = moves = 0
    for r in range(min(h, len(y))):
        for j in range(r + h, len(y), h):
            key = y[j]
            i = j - h
            while i >= r:
                comparisons += 1
                if y[i] > key:
                    y[i + h] = y[i]
                    moves += 1
                    i -= h
                else:
                    break
            y[i + h] = key
    return tuple(y), moves, comparisons


def rank_pair_costs(x, h):
    """Compute the proposed formula on the array entering the pass."""
    inversions = []
    stops = []
    same_chain = []
    for r in range(min(h, len(x))):
        chain = x[r::h]
        for j, current in enumerate(chain):
            for old in chain[:j]:
                same_chain.append((old, current))
                if old > current:
                    inversions.append((old, current))
            if j:
                earlier_minimum = min(chain[:j])
                if current > earlier_minimum:
                    stops.append((current, earlier_minimum))
    return inversions, stops, same_chain


def all_contiguous_partitions(n):
    """Represent a partition by boundaries including 0 and n."""
    for mask in range(1 << (n - 1)):
        yield (0,) + tuple(i for i in range(1, n) if mask & (1 << (i - 1))) + (n,)


def equal_buckets(n, b):
    return tuple(range(0, n, b)) + (n,)


def bucket_information(boundaries):
    sizes = [b - a for a, b in zip(boundaries, boundaries[1:])]
    ids = tuple(k for k, size in enumerate(sizes) for _ in range(size))
    return ids, max(sizes), sum(size * (size - 1) // 2 for size in sizes)


def truncated_pairs(inversions, stops, bucket_ids):
    m = sum(bucket_ids[a] != bucket_ids[b] for a, b in inversions)
    c = m + sum(bucket_ids[a] != bucket_ids[b] for a, b in stops)
    return m, c


def tree_nodes(boundaries):
    """Balanced binary tree on consecutive rank buckets."""
    def visit(first, last):
        if last - first <= 1:
            return
        middle = (first + last) // 2
        yield boundaries[first], boundaries[middle], boundaries[last]
        yield from visit(first, middle)
        yield from visit(middle, last)
    return tuple(visit(0, len(boundaries) - 1))


def rank_tree_indicator(a, b, boundaries):
    return sum((int(a < u) - int(a < m)) * (int(b < m) - int(b < l))
               for l, m, u in tree_nodes(boundaries))


def first_pass_means(n, h, boundaries):
    """Closed formulas for the first pass, including truncated comparisons."""
    same_pairs = sum(comb(b - a, 2) for a, b in zip(boundaries, boundaries[1:]))
    cross_pairs = comb(n, 2) - same_pairs
    inversion_probability = Fraction(cross_pairs, n * (n - 1)) if n > 1 else Fraction(0)
    m = sum(comb(length, 2) * inversion_probability for length in chain_lengths(n, h))
    c = m
    for length in chain_lengths(n, h):
        for j in range(1, length):
            stop_probability = sum(
                Fraction((u - l) * (comb(n - 1, j) - comb(n - 1 - l, j)), n * comb(n - 1, j))
                for l, u in zip(boundaries, boundaries[1:])
            )
            c += stop_probability
    return m, c


def full_first_pass_means(n, h):
    m = sum(Fraction(length * (length - 1), 4) for length in chain_lengths(n, h))
    c = m + sum(length - sum(Fraction(1, j) for j in range(1, length + 1))
                for length in chain_lengths(n, h))
    return m, c


def check_rank_tree_identity():
    cases = 0
    for n in range(1, 11):
        for boundaries in all_contiguous_partitions(n):
            ids, _, _ = bucket_information(boundaries)
            for a in range(n):
                for b in range(n):
                    assert rank_tree_indicator(a, b, boundaries) == int(a > b and ids[a] != ids[b])
                    cases += 1
    return {"maximum_n": 10, "all_contiguous_partitions": True, "ordered_rank_pair_cases": cases}


def exhaustive_single_pass():
    result = []
    strongest_q_constant = Fraction(0)
    strongest_q_witness = None
    max_footrule_ratio = Fraction(0)
    total_permutations = total_passes = total_bucket_checks = 0
    total_q_finite_checks = total_q_constant_checks = 0
    for n in range(1, 8):
        partitions = tuple(all_contiguous_partitions(n)) if n <= 6 else tuple(dict.fromkeys(equal_buckets(n, b) for b in range(1, n + 1)))
        info = {boundaries: bucket_information(boundaries) for boundaries in partitions}
        q_finite = {}
        for h in range(1, n + 1):
            for boundaries in partitions:
                _, b, _ = info[boundaries]
                if h >= b:
                    q_finite[h, boundaries] = 4 * sum((Fraction(1, (k * h - b + 1) ** 2)
                                                     for k in range(1, (n - 1) // h + 1)), Fraction(0))
        sums = defaultdict(lambda: [0, 0])
        truncated_sums = defaultdict(lambda: [0, 0])
        cases = 0
        for x in permutations(range(n)):
            total_permutations += 1
            F = sum(abs(v - i) for i, v in enumerate(x))
            Q = sum((v - i) ** 2 for i, v in enumerate(x))
            for h in range(1, n + 1):
                _, moves, comparisons = insertion_pass(x, h)
                inv, stops, pairs = rank_pair_costs(x, h)
                assert moves == len(inv), ("move_identity", n, x, h)
                assert comparisons == len(inv) + len(stops), ("comparison_identity", n, x, h)
                assert len({tuple(sorted(pair)) for pair in inv + stops}) == len(inv) + len(stops), ("pair_disjointness", n, x, h)
                sums[h][0] += moves
                sums[h][1] += comparisons
                total_passes += 1
                for boundaries in partitions:
                    ids, b, bucket_capacity = info[boundaries]
                    trunc_m, trunc_c = truncated_pairs(inv, stops, ids)
                    U = sum(ids[a] == ids[b_] for a, b_ in pairs)
                    assert 0 <= comparisons - trunc_c <= U, ("truncation", n, x, h, boundaries)
                    assert U <= bucket_capacity, ("bucket_capacity", n, x, h, boundaries)
                    assert 2 * bucket_capacity <= n * (b - 1), ("max_bucket_size", n, boundaries)
                    assert U * h <= 2 * F + n * (b - 1), ("footrule_bound", n, x, h, boundaries, U, F)
                    if 2 * F + n * (b - 1):
                        max_footrule_ratio = max(max_footrule_ratio, Fraction(U * h, 2 * F + n * (b - 1)))
                    if h >= b:
                        rhs = q_finite[h, boundaries]
                        assert U * rhs.denominator <= Q * rhs.numerator, ("finite_q_bound", n, x, h, boundaries, U, Q)
                        total_q_finite_checks += 1
                    if h >= 2 * b:
                        # This is stronger than 8*pi^2/3, because pi > 3.
                        assert U * h * h <= 24 * Q, ("stronger_q_constant_bound", n, x, h, boundaries, U, Q)
                        total_q_constant_checks += 1
                        if Q and Fraction(U * h * h, Q) > strongest_q_constant:
                            strongest_q_constant = Fraction(U * h * h, Q)
                            strongest_q_witness = {"n": n, "permutation": x, "h": h, "boundaries": boundaries, "U": U, "Q": Q}
                    truncated_sums[h, boundaries][0] += trunc_m
                    truncated_sums[h, boundaries][1] += trunc_c
                    cases += 1
                    total_bucket_checks += 1
        denom = factorial(n)
        for h in range(1, n + 1):
            observed = tuple(Fraction(v, denom) for v in sums[h])
            assert observed == full_first_pass_means(n, h), ("first_pass_means", n, h, observed)
            for boundaries in partitions:
                obs = tuple(Fraction(v, denom) for v in truncated_sums[h, boundaries])
                assert obs == first_pass_means(n, h, boundaries), ("truncated_first_pass_means", n, h, boundaries, obs)
        result.append({"n": n, "permutations": denom, "gaps": n, "partitions": len(partitions), "bucket_checks": cases,
                       "partition_scope": "all contiguous partitions" if n <= 6 else "equal-width buckets of every possible width"})
    return {"per_n": result, "permutations": total_permutations, "single_passes": total_passes,
            "bucket_checks": total_bucket_checks, "finite_q_bound_checks": total_q_finite_checks,
            "stronger_24_q_bound_checks": total_q_constant_checks,
            "max_observed_Uh2_over_Q_when_h_ge_2b": frac_text(strongest_q_constant),
            "q_ratio_witness": strongest_q_witness, "max_footrule_rhs_fraction": frac_text(max_footrule_ratio)}


def selected_words(n):
    words = [(n, 1, n, 1), (min(2, n), min(3, n), min(2, n), 1),
             (min(3, n), min(2, n), min(3, n), 1), (max(1, n - 1), max(1, n // 2), 1)]
    return tuple(dict.fromkeys(words))


def exhaustive_words():
    cases = 0
    pass_steps = 0
    mean_results = []
    for n in range(2, 7):
        for word in selected_words(n):
            totals = [0, 0]
            for x0 in permutations(range(n)):
                x = x0
                full = 0
                cut = [0] * n
                capacity = [0] * n
                for h in word:
                    inv, stops, pairs = rank_pair_costs(x, h)
                    after, moves, comparisons = insertion_pass(x, h)
                    full += comparisons
                    totals[0] += moves
                    totals[1] += comparisons
                    for b in range(1, n + 1):
                        ids, _, _ = bucket_information(equal_buckets(n, b))
                        cut[b - 1] += truncated_pairs(inv, stops, ids)[1]
                        capacity[b - 1] += sum(ids[a] == ids[b_] for a, b_ in pairs)
                    x = after
                    pass_steps += 1
                for b in range(1, n + 1):
                    assert 0 <= full - cut[b - 1] <= capacity[b - 1]
                    assert 2 * (full - cut[b - 1]) <= len(word) * n * (b - 1)
                    cases += 1
            mean_results.append({"n": n, "word": word, "mean_moves": frac_text(Fraction(totals[0], factorial(n))),
                                 "mean_comparisons": frac_text(Fraction(totals[1], factorial(n)))})
    return {"bucket_word_cases": cases, "pass_steps": pass_steps, "mean_results": mean_results}


def check_independent_marginals():
    outputs = [insertion_pass(x, 2)[0] for x in permutations(range(4))]
    marginals = [Counter(x[i] for x in outputs) for i in range(4)]
    results = []
    for left, right in ((0, 1), (0, 2)):
        actual = Fraction(sum(x[left] > x[right] for x in outputs), len(outputs))
        product = sum((Fraction(ca * cb, len(outputs) ** 2) for a, ca in marginals[left].items()
                       for b, cb in marginals[right].items() if a > b), Fraction(0))
        results.append({"positions": [left, right], "actual_inversion_probability": frac_text(actual),
                        "product_marginal_probability": frac_text(product)})
    assert results[0]["actual_inversion_probability"] == "1/2"
    assert results[0]["product_marginal_probability"] == "11/36"
    assert results[1]["actual_inversion_probability"] == "0"
    assert results[1]["product_marginal_probability"] == "1/36"
    return results


def check_truncation_interpretation():
    """The prefix-min proxy is not the actual failed-comparison endpoint."""
    x = (0, 1, 2)
    ids, _, _ = bucket_information((0, 1, 3))
    inv, stops, _ = rank_pair_costs(x, 1)
    represented_cross_bucket_count = truncated_pairs(inv, stops, ids)[1]
    # On an already increasing chain, actual comparisons are adjacent keys.
    actual_cross_bucket_count = sum(ids[a] != ids[b] for a, b in ((1, 0), (2, 1)))
    assert represented_cross_bucket_count == 2
    assert actual_cross_bucket_count == 1

    y = (2, 1, 0)
    ids2, _, _ = bucket_information((0, 2, 3))
    inv2, stops2, _ = rank_pair_costs(y, 1)
    represented2 = truncated_pairs(inv2, stops2, ids2)[1]
    labels = tuple(ids2[v] for v in y)
    collapsed_label_cost = insertion_pass(labels, 1)[2]
    assert represented2 == 2
    assert collapsed_label_cost == 3
    return {
        "actual_trace_counterexample": {"permutation": x, "gap": 1, "bucket_boundaries": [0, 1, 3],
                                         "representation_truncation": represented_cross_bucket_count,
                                         "actual_cross_bucket_comparisons": actual_cross_bucket_count},
        "collapsed_labels_counterexample": {"permutation": y, "gap": 1, "bucket_boundaries": [0, 2, 3],
                                            "representation_truncation": represented2,
                                            "comparison_count_on_collapsed_labels": collapsed_label_cost},
    }


def three_color_states(n, first_gap, s, t):
    """All feasible first-pass chain color counts, with exact multiplicities."""
    low, high = sorted((s, t))
    targets = (low, high - low, n - high)
    lengths = chain_lengths(n, first_gap)
    denominator = factorial(n) // (factorial(targets[0]) * factorial(targets[1]) * factorial(targets[2]))

    def generate(chain, remaining, weight, triples):
        if chain == len(lengths):
            if remaining != (0, 0, 0):
                return
            colors = [None] * n
            for r, counts in enumerate(triples):
                values = [0] * counts[0] + [1] * counts[1] + [2] * counts[2]
                for pos, value in zip(range(r, n, first_gap), values):
                    colors[pos] = value
            yield tuple(colors), Fraction(weight, denominator)
            return
        length = lengths[chain]
        for a in range(min(length, remaining[0]) + 1):
            for b in range(min(length - a, remaining[1]) + 1):
                c = length - a - b
                if c > remaining[2]:
                    continue
                multiplicity = comb(length, a) * comb(length - a, b)
                yield from generate(chain + 1, (remaining[0] - a, remaining[1] - b, remaining[2] - c),
                                    weight * multiplicity, triples + ((a, b, c),))
    return tuple(generate(0, targets, 1, ()))


def color_indicator(color, threshold, low, high):
    if threshold == low:
        return int(color == 0)
    assert threshold == high
    return int(color <= 1)


def two_threshold_kernel(colors, h, s, t):
    """Return successful-pair and prefix-min kernels from a joint color state."""
    low, high = sorted((s, t))
    inv = stops = 0
    for r in range(min(h, len(colors))):
        past_s_count = 0
        past_t_any = 0
        for color in colors[r::h]:
            xs = color_indicator(color, s, low, high)
            xt = color_indicator(color, t, low, high)
            inv += past_s_count * xt
            stops += xs * past_t_any
            past_s_count += xs
            past_t_any = max(past_t_any, xt)
    return inv, stops


def sort_color_pass(colors, h):
    out = list(colors)
    for r in range(min(h, len(out))):
        chain = out[r::h]
        counts = [chain.count(color) for color in range(3)]
        out[r::h] = [0] * counts[0] + [1] * counts[1] + [2] * counts[2]
    return tuple(out)


def exact_three_color_means(n, word, boundaries):
    """First pass separately; all later costs reconstructed by joint kernels."""
    coefficients = Counter()
    for l, m, u in tree_nodes(boundaries):
        coefficients[u, m] += 1
        coefficients[u, l] -= 1
        coefficients[m, m] -= 1
        coefficients[m, l] += 1
    coefficients = {pair: coefficient for pair, coefficient in coefficients.items() if coefficient}
    by_pass = [[Fraction(0), Fraction(0)] for _ in word]
    by_pass[0][:] = first_pass_means(n, word[0], boundaries)
    state_visits = 0
    max_mass_error = Fraction(0)
    for (s, t), coefficient in coefficients.items():
        states = three_color_states(n, word[0], s, t)
        mass = sum((prob for _, prob in states), Fraction(0))
        max_mass_error = max(max_mass_error, abs(mass - 1))
        assert mass == 1, ("three_color_mass", n, word[0], s, t, mass)
        state_visits += len(states)
        for colors0, probability in states:
            colors = colors0
            for r, h in enumerate(word[1:], start=1):
                inv, stops = two_threshold_kernel(colors, h, s, t)
                by_pass[r][0] += coefficient * probability * inv
                by_pass[r][1] += coefficient * probability * (inv + stops)
                colors = sort_color_pass(colors, h)
    return tuple(tuple(row) for row in by_pass), len(coefficients), state_visits


def full_permutation_means_by_pass(n, word, boundaries):
    sums = [[0, 0] for _ in word]
    ids, _, _ = bucket_information(boundaries)
    for x0 in permutations(range(n)):
        x = x0
        for r, h in enumerate(word):
            inv, stops, _ = rank_pair_costs(x, h)
            m, c = truncated_pairs(inv, stops, ids)
            sums[r][0] += m
            sums[r][1] += c
            x = insertion_pass(x, h)[0]
    return tuple(tuple(Fraction(v, factorial(n)) for v in row) for row in sums)


def check_three_color_enumeration():
    checks = []
    for n in range(2, 7):
        for word in selected_words(n):
            for b in sorted({1, 2, min(3, n), n}):
                boundaries = equal_buckets(n, b)
                computed, pair_count, state_visits = exact_three_color_means(n, word, boundaries)
                observed = full_permutation_means_by_pass(n, word, boundaries)
                assert computed == observed, ("three_color_mean", n, word, boundaries, computed, observed)
                checks.append({"n": n, "word": word, "bucket_width": b, "threshold_pairs": pair_count,
                               "feasible_first_pass_states_over_threshold_pairs": state_visits,
                               "pass_means": [{"moves": frac_text(m), "comparisons": frac_text(c)} for m, c in computed]})
    return {"word_bucket_checks": len(checks), "exact_pass_mean_checks": sum(len(row["word"]) for row in checks),
            "records": checks}


def main():
    start = time.perf_counter()
    result = {
        "status": "running",
        "model": {"input": "uniform permutations of distinct ranks 0,...,n-1",
                  "gap_words": "fixed in advance; repeated and increasing gaps included",
                  "comparisons": "key comparisons in ordinary chain insertion, excluding boundary tests",
                  "moves": "successful shift operations, one per entering chain inversion",
                  "bucket_cost": "cross-bucket terms of the inversion-plus-prefix-min formula; neither the actual cross-bucket comparison trace nor sorting bucket labels"},
        "scope": "Finite exact verification. General analytic theorems require separate proofs.",
    }
    stages = [
        ("rank_tree", check_rank_tree_identity),
        ("single_pass", exhaustive_single_pass),
        ("gap_words", exhaustive_words),
        ("independent_marginal_counterexample", check_independent_marginals),
        ("truncation_interpretation", check_truncation_interpretation),
        ("three_color_enumeration", check_three_color_enumeration),
    ]
    for name, operation in stages:
        before = time.perf_counter()
        result[name] = operation()
        result[name + "_seconds"] = round(time.perf_counter() - before, 6)
        print(f"PASS {name}: {result[name + '_seconds']:.3f}s", flush=True)
    result["status"] = "passed"
    result["total_seconds"] = round(time.perf_counter() - start, 6)
    (HERE / "verification_results.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {HERE / 'verification_results.json'}", flush=True)


if __name__ == "__main__":
    main()
