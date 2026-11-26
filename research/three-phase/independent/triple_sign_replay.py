"""Compare the g=3 Fourier certificate against the two physical arcs separately."""
from fractions import Fraction as F
from functools import cache
from itertools import permutations
from math import comb, factorial
import triple_sign_certificate as cert
from four_three_certificate import Cyclo, bernstein


@cache
def residue_counts(s, h, length, t):
    a, b = t.numerator, t.denominator
    counts = [0, 0, 0]
    for x in range(length + 1):
        counts[(s + h * x) % 3] += comb(length, x) * a**x * (b-a)**(length-x)
    assert sum(counts) == b**length
    return counts


def physical(n, h, t):
    """Exact integer probability weights on the owner's and all nonowners' true chains."""
    m, r = divmod(n, h)
    b = t.denominator
    lengths = [m + (s < r) for s in range(h)]
    counts = [residue_counts(s, h, L, t) for s, L in enumerate(lengths)]
    total = 0
    for o, Lo in enumerate(lengths):
        if not Lo:
            continue
        for j, owner_count in enumerate(residue_counts(o, h, Lo-1, t)):
            if not owner_count:
                continue
            for width in (1, 2):
                arc = [(j + h * k) % 3 for k in range(1, width+1)]
                law = [1]
                for s, L in enumerate(lengths):
                    if s == o:
                        continue
                    hit = sum(counts[s][x] for x in arc)
                    miss = b**L - hit
                    nxt = [0] * (len(law)+1)
                    for i, value in enumerate(law):
                        nxt[i] += miss * value
                        nxt[i+1] += hit * value
                    law = nxt
                center = h * width // 3
                total += Lo * owner_count * sum(abs(i-center)*v for i, v in enumerate(law))
    return cert.psi(h) - F(total, 2*n*b**(n-1))


def spectral(n, h, t):
    m, r = divmod(n, h)
    one, uniform = cert.nodal_polynomials(h, r, t.numerator, t.denominator)
    z = Cyclo(1-t) + Cyclo(*cert.ROOTS[h%3]) * t
    y = z**m
    result = F(0)
    for (i, j), value in one.items():
        weight = cert.add(value, cert.scale(uniform[i, j], m-1))
        contribution = (Cyclo(*weight) * y**i * y.bar()**j).re()
        result += (1 if i == j else 2) * contribution
    return result / (2*3**(h-1)*n*t.denominator**(h+2)*z.norm())


def key_rank_deficits(n, h):
    total = [0]*n
    for arr in permutations(range(n)):
        out = list(arr)
        for gap in (h, 3):
            for s in range(gap):
                out[s::gap] = sorted(out[s::gap])
        for i, x in enumerate(out):
            for j in range(i+1, n):
                if x > out[j]:
                    total[x] += 1
                    total[out[j]] += 1
    return [cert.psi(h) - F(v, 2*factorial(n)) for v in total]


if __name__ == "__main__":
    checks = 0
    for h in (2, 4, 5, 7, 8, 10, 11, 13, 14):
        for m in (1, 2, 5):
            for r in range(h):
                n = h*m + r
                for t in (F(0), F(1,5), F(1,2), F(4,5), F(1)):
                    target = physical(n, h, t)
                    actual = spectral(n, h, t)
                    assert actual == target, (n, h, t, actual, target)
                    assert target > 0, (n, h, t, target)
                    checks += 1
    print(f"Coefficient formula and physical two-arc convolution agree at {checks} exact rational inputs.")
    checks = 0
    for n in range(1,9):
        for h in (2,4,5,7,8):
            by_rank = key_rank_deficits(n, h)
            integrated = physical(n, h, F()) if n == 1 else sum(bernstein(
                [physical(n, h, F(i,n-1)) for i in range(n)]), F())/n
            assert integrated == sum(by_rank, F())/n
            checks += 1
    pivot = key_rank_deficits(7,4)[3]
    assert pivot == -F(41,1890)
    print(f"Physical conditional formula matches exhaustive sorted permutations at {checks} pairs.")
    print(f"At n=7,h=4, the key of zero-based rank 3 has finite-rank deficit {pivot}.")
