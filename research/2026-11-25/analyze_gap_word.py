#!/usr/bin/env python3
"""Research prototype: exact two-threshold analysis of a fixed gap word.

Example:
    python analyze_gap_word.py --n 6 --gaps 5,3,1 --bucket-width 2 \
        --verify-permutations --output demo_n6_gaps_5_3_1_b2.json

Default execution enumerates feasible three-color count states after the first
pass, never full input permutations.  --verify-permutations is an optional,
independent demonstration check restricted to n <= 8.  This analyzer can require
exponential time.  Its execution time is not the Shellsort time being analyzed.
"""

import argparse
from collections import Counter
from fractions import Fraction
from itertools import permutations
from math import comb, factorial, prod
from pathlib import Path
import json
import sys
import time

from verify_joint_framework import (
    bucket_information,
    chain_lengths,
    equal_buckets,
    exact_three_color_means,
    frac_text,
    full_first_pass_means,
    insertion_pass,
    rank_pair_costs,
    tree_nodes,
    truncated_pairs,
)


def parse_arguments():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--n", type=int, required=True, help="number of distinct ranks, at least 1")
    parser.add_argument("--gaps", required=True, help="fixed gap word, e.g. 5,3,1; repeated/increasing gaps are allowed")
    parser.add_argument("--bucket-width", type=int, default=1, help="consecutive rank bucket width; 1 gives the exact total mean")
    parser.add_argument("--verify-permutations", action="store_true", help="independently run every permutation; allowed only for n <= 8")
    parser.add_argument("--output", type=Path, help="also save the JSON report to this path")
    args = parser.parse_args()
    if args.n < 1:
        parser.error("--n must be positive")
    if args.bucket_width < 1:
        parser.error("--bucket-width must be positive")
    try:
        args.word = tuple(int(value.strip()) for value in args.gaps.split(","))
    except ValueError:
        parser.error("--gaps must be a nonempty comma-separated list of integers")
    if not args.word or any(h < 1 or h > args.n for h in args.word):
        parser.error("each gap must lie in 1,...,n")
    if args.verify_permutations and args.n > 8:
        parser.error("--verify-permutations is restricted to n <= 8; omit it to use only the state analyzer")
    return args


def threshold_coefficients(boundaries):
    result = Counter()
    for l, m, u in tree_nodes(boundaries):
        result[u, m] += 1
        result[u, l] -= 1
        result[m, m] -= 1
        result[m, l] += 1
    return {pair: coefficient for pair, coefficient in result.items() if coefficient}


def verify_means(n, word, boundaries, proxy_means, bucket_capacity):
    """Optional direct insertion check; not part of the default analyzer."""
    ids, _, _ = bucket_information(boundaries)
    totals = [[0, 0] for _ in word]
    proxy_totals = [[0, 0] for _ in word]
    for x0 in permutations(range(n)):
        x = x0
        for r, h in enumerate(word):
            inv, stops, _ = rank_pair_costs(x, h)
            trunc_m, trunc_c = truncated_pairs(inv, stops, ids)
            x, moves, comparisons = insertion_pass(x, h)
            totals[r][0] += moves
            totals[r][1] += comparisons
            proxy_totals[r][0] += moves if r == 0 else trunc_m
            proxy_totals[r][1] += comparisons if r == 0 else trunc_c
    denominator = factorial(n)
    actual = tuple(tuple(Fraction(v, denominator) for v in row) for row in totals)
    enumerated_proxy = tuple(tuple(Fraction(v, denominator) for v in row) for row in proxy_totals)
    assert enumerated_proxy == proxy_means, ("proxy_mean_disagreement", enumerated_proxy, proxy_means)
    for r, (actual_row, proxy_row) in enumerate(zip(actual, proxy_means)):
        cap = 0 if r == 0 else bucket_capacity
        for exact, approx in zip(actual_row, proxy_row):
            assert approx <= exact <= approx + cap, ("per_pass_interval", r, exact, approx, cap)
    totals_actual = tuple(sum((row[k] for row in actual), Fraction(0)) for k in range(2))
    totals_proxy = tuple(sum((row[k] for row in proxy_means), Fraction(0)) for k in range(2))
    cap = (len(word) - 1) * bucket_capacity
    for exact, approx in zip(totals_actual, totals_proxy):
        assert approx <= exact <= approx + cap
    return {
        "performed": True,
        "permutations": denominator,
        "direct_insertion_passes": denominator * len(word),
        "all_proxy_means_match": True,
        "all_actual_means_inside_certified_intervals": True,
        "actual_per_pass_means": [
            {"pass": r + 1, "gap": word[r], "moves": frac_text(m), "comparisons": frac_text(c)}
            for r, (m, c) in enumerate(actual)
        ],
        "actual_total_mean_moves": frac_text(totals_actual[0]),
        "actual_total_mean_comparisons": frac_text(totals_actual[1]),
        "total_mean_move_error": frac_text(totals_actual[0] - totals_proxy[0]),
        "total_mean_comparison_error": frac_text(totals_actual[1] - totals_proxy[1]),
    }


def main():
    args = parse_arguments()
    started = time.perf_counter()
    n, word = args.n, args.word
    boundaries = equal_buckets(n, args.bucket_width)
    _, actual_max_bucket, bucket_capacity = bucket_information(boundaries)
    lengths = chain_lengths(n, word[0])
    state_cap = prod(comb(length + 2, 2) for length in lengths)
    pair_count = len(threshold_coefficients(boundaries)) if len(word) > 1 else 0
    work_cap = pair_count * state_cap
    if work_cap > 1_000_000:
        print(
            f"Warning: exponential research analyzer; loose state-visit upper bound is {work_cap:,}. "
            "This is analysis work, not the Shellsort running time.",
            file=sys.stderr,
        )

    first_full = full_first_pass_means(n, word[0])
    if len(word) > 1:
        truncated, actual_pair_count, actual_state_visits = exact_three_color_means(n, word, boundaries)
        assert actual_pair_count == pair_count
        proxy_means = (first_full,) + truncated[1:]
    else:
        actual_state_visits = 0
        proxy_means = (first_full,)
    assert actual_state_visits <= work_cap
    total_proxy = tuple(sum((row[k] for row in proxy_means), Fraction(0)) for k in range(2))
    additive_bound = (len(word) - 1) * bucket_capacity
    total_upper = tuple(value + additive_bound for value in total_proxy)

    report = {
        "schema_version": 1,
        "prototype_status": "reviewable research prototype; not a production optimization library",
        "model": {
            "uniform_random_permutations": True,
            "distinct_ranks": "0,...,n-1",
            "gaps_fixed_independently_of_input": True,
            "repeated_and_increasing_gaps_allowed": True,
            "algorithm": "ordinary chain insertion, no sentinel",
            "comparisons": "key comparisons including final failed comparisons; boundary/index operations excluded",
            "moves": "successful shifts, excluding key restoration assignments",
            "final_gap_one_sufficient_for_sorting": True,
            "this_word_has_final_gap_one": word[-1] == 1,
            "this_word_contains_gap_one_and_thus_sorts": 1 in word,
        },
        "input": {"n": n, "gaps": word, "passes": len(word), "requested_bucket_width": args.bucket_width,
                  "bucket_boundaries": boundaries, "largest_bucket_size": actual_max_bucket,
                  "number_of_buckets": len(boundaries) - 1, "B0_same_bucket_unordered_pairs": bucket_capacity},
        "method": {
            "arithmetic": "exact rational",
            "after_first_pass": "enumerate feasible joint two-threshold / three-color chain-count states with exact multinomial weights",
            "first_pass": "handled separately by full_first_pass_means; its original order is not reconstructed from sorted color counts",
            "tail_proxy": "cross-bucket terms of inversions plus STRICT current-rank > prefix-min-rank indicators",
            "proxy_is_actual_cross_bucket_trace": False,
            "proxy_is_insertion_comparisons_on_repeated_bucket_labels": False,
            "default_enumerates_full_permutations": False,
            "per_threshold_pair_state_cap": state_cap,
            "state_cap_formula": "product_r binomial(L_r+2,2), for first-pass chain lengths L_r; ignores global color-count constraints",
            "first_pass_chain_lengths": lengths,
            "threshold_pairs_used": pair_count,
            "state_visit_upper_bound": work_cap,
            "actual_feasible_state_visits_over_threshold_pairs": actual_state_visits,
            "arithmetic_work_scale_upper_bound": work_cap * len(word) * n,
            "time_complexity_note": "Potentially exponential. O(K*p*n*product_r binomial(L_r+2,2)) arithmetic work; exact big-integer costs are additional. Analyzer time is not Shellsort time.",
        },
        "per_pass": [
            {"pass": r + 1, "gap": word[r], "mean_type": "exact first-pass mean" if r == 0 else "exact mean of bucket proxy",
             "mean_moves": frac_text(m), "mean_comparisons": frac_text(c),
             "additive_error_bound_each_cost": 0 if r == 0 else bucket_capacity,
             "comparison_mean_interval": [frac_text(c), frac_text(c + (0 if r == 0 else bucket_capacity))]}
            for r, (m, c) in enumerate(proxy_means)
        ],
        "total": {
            "first_exact_plus_tail_proxy_moves": frac_text(total_proxy[0]),
            "first_exact_plus_tail_proxy_comparisons": frac_text(total_proxy[1]),
            "additive_error_bound_each_cost": additive_bound,
            "bound_formula": "(p-1)*B0; B0=sum_B binomial(|B|,2) <= n*(b-1)/2",
            "mean_move_interval": [frac_text(total_proxy[0]), frac_text(total_upper[0])],
            "mean_comparison_interval": [frac_text(total_proxy[1]), frac_text(total_upper[1])],
            "means_exact_when_intervals_collapse": additive_bound == 0,
        },
        "verification": {"performed": False},
    }
    if args.verify_permutations:
        report["verification"] = verify_means(n, word, boundaries, proxy_means, bucket_capacity)
    report["analyzer_elapsed_seconds"] = round(time.perf_counter() - started, 6)
    text = json.dumps(report, ensure_ascii=False, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    sys.stdout.write(text)


if __name__ == "__main__":
    main()
