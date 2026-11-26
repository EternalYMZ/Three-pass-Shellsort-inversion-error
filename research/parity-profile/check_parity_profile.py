"""Exact and high-precision regression for the uniform Shellsort parity profile."""

from collections import defaultdict
from decimal import Decimal, getcontext
from fractions import Fraction
from functools import cache
from itertools import permutations
from math import comb, cos, factorial, pi


getcontext().prec = 65
PI = Decimal("3.141592653589793238462643383279502884197169399375105820974944592307816")
NORMALIZER = 2 * (2 * PI).sqrt()


def to_decimal(value):
    return Decimal(value.numerator) / Decimal(value.denominator)


def exact_deficit(n, h):
    """Integrate the symmetric-step probabilities as polynomials in y=|1-2t|."""
    assert n >= h >= 3 and h % 2
    r = (h - 1) // 2
    m, remainder = divmod(n, h)
    pair_lengths = [m + 1] * (remainder // 2) + [m] * ((h - remainder) // 2)
    assert len(pair_lengths) == r

    coefficients = {(0, 0): 1}
    for length in pair_lengths:
        product = defaultdict(int)
        for (position, power), coefficient in coefficients.items():
            for step, constant, raised in ((-1, 1, -1), (0, 2, 2), (1, 1, -1)):
                product[position + step, power] += coefficient * constant
                product[position + step, power + length] += coefficient * raised
        coefficients = {key: value for key, value in product.items() if value}

    moment = defaultdict(int)
    mass = defaultdict(int)
    for (position, power), coefficient in coefficients.items():
        moment[power] += abs(position) * coefficient
        mass[power] += coefficient
    assert {key: value for key, value in mass.items() if value} == {0: 4**r}
    fair_mean = Fraction(r * comb(2 * r, r), 4**r)
    assert Fraction(moment[0], 4**r) == fair_mean  # t=1/2, all steps are fair
    assert sum(moment.values()) == 0  # t=0,1, all steps vanish
    integrated = sum(Fraction(value, 2 * power + 1) for power, value in moment.items()) / 4**r
    actual = Fraction(n + 1, 2) * integrated
    reference = Fraction(n, 2) * fair_mean
    return reference - actual, actual


def insert(state, gap):
    moves = 0
    for i in range(gap, len(state)):
        key = state[i]
        j = i
        while j >= gap and state[j - gap] > key:
            state[j] = state[j - gap]
            j -= gap
            moves += 1
        state[j] = key
    return moves


def physical_mean(n, h):
    shifts = 0
    for order in permutations(range(n)):
        state = list(order)
        insert(state, h)
        insert(state, 2)
        shifts += insert(state, 1)
    return Fraction(shifts, factorial(n))


def legendre_value_and_derivative(degree, x):
    previous = Decimal(1)
    current = x
    for k in range(2, degree + 1):
        previous, current = current, ((2 * k - 1) * x * current - (k - 1) * previous) / k
    derivative = degree * (previous - x * current) / (1 - x * x)
    return current, derivative


@cache
def quadrature(degree):
    """Gauss-Legendre nodes and weights on [0,1], computed in Decimal arithmetic."""
    assert degree % 2 == 0
    result = []
    for j in range(1, degree // 2 + 1):
        x = Decimal(str(cos(pi * (j - 0.25) / (degree + 0.5))))
        for _ in range(12):
            value, derivative = legendre_value_and_derivative(degree, x)
            correction = value / derivative
            x -= correction
            if abs(correction) < Decimal("1e-60"):
                break
        else:
            raise ArithmeticError("Legendre root failed to converge")
        _, derivative = legendre_value_and_derivative(degree, x)
        weight = 1 / ((1 - x * x) * derivative**2)
        result.extend([((1 - x) / 2, weight), ((1 + x) / 2, weight)])
    assert abs(sum(w for _, w in result) - 1) < Decimal("1e-60")
    return result


def profile(rho, degree):
    m = rho.numerator // rho.denominator
    theta = to_decimal(rho - m)
    integral = Decimal(0)
    for u, weight in quadrature(degree):
        y = 1 - u * u
        p = y ** (2 * m) * (1 - theta + theta * y * y)
        # y=1-u^2 removes the square-root endpoint; the fraction avoids cancellation.
        integral += weight * 2 * u * p / (1 + (1 - p).sqrt())
    return to_decimal(rho) * integral / NORMALIZER


def explicit_error(h):
    r = (h - 1) // 2
    return ((2 + Decimal(r).ln()) / Decimal(r).sqrt()
            + 1 / (PI * (h - 1)).sqrt() + 1 / Decimal(2 * h))


def main():
    executions = triples = 0
    for n in range(3, 9):
        for h in range(3, n + 1, 2):
            deficit, actual = exact_deficit(n, h)
            assert physical_mean(n, h) == actual
            assert deficit > 0
            executions += factorial(n)
            triples += 1
    print(f"Exact polynomial integration matches insertion on {executions} permutations/tables "
          f"for all {triples} parity triples with 3 <= h <= n <= 8.")

    endpoint = (1 - PI / 4) / NORMALIZER
    limit = (1 - Decimal(2).ln()) / NORMALIZER
    examples = [(3, 3), (4, 3), (5, 5), (20, 5), (31, 31), (46, 31),
                (61, 31), (62, 31), (63, 31), (93, 31), (3100, 31)]
    print(" n     h    rho                 D/h^(3/2)           C(rho)")
    for n, h in examples:
        rho = Fraction(n, h)
        deficit, _ = exact_deficit(n, h)
        scaled = to_decimal(deficit) / (h * Decimal(h).sqrt())
        coarse = profile(rho, 96)
        value = profile(rho, 160)
        assert abs(coarse - value) < Decimal("1e-29")
        assert abs(scaled - value) < explicit_error(h)
        if rho > 1:
            assert endpoint < value < limit
        assert limit - value < 1 / (4 * NORMALIZER * to_decimal(rho))
        print(f"{n:4} {h:5}  {str(rho):>7}     {scaled:.16f}    {value:.16f}")
        if h <= 5:
            print(f"              exact D = {deficit}")

    assert abs(profile(Fraction(1), 128) - endpoint) < Decimal("1e-55")
    epsilon = Fraction(1, 10**7)
    for m in (1, 2, 3, 8):
        at_integer = profile(Fraction(m), 96)
        assert profile(m + epsilon, 96) > at_integer
        if m > 1:
            assert profile(m - epsilon, 96) > at_integer
    print("Checked the strict global bounds on all sampled ratios and the one-sided "
          "increases away from m=1, 2, 3, 8 with step 1e-7.")
    print(f"C(1)   = {endpoint:.25f}")
    print(f"C(inf) = {limit:.25f}")


if __name__ == "__main__":
    main()
