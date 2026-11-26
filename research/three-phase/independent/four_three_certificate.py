"""Rational certificate of the all-size Janson–Knuth sign for gaps (4,3).
All polynomial tests use exact Q(omega) arithmetic and Bernstein coefficients.
The optional direct regression executes ordinary gap insertion on permutations.
"""
from fractions import Fraction as F
from itertools import combinations, permutations
from math import comb, factorial


class Cyclo:
    """a + b*omega, where omega^2+omega+1=0."""
    def __init__(self, a=0, b=0):
        self.a, self.b = F(a), F(b)

    def __add__(self, other):
        if not isinstance(other, Cyclo):
            other = Cyclo(other)
        return Cyclo(self.a+other.a, self.b+other.b)

    __radd__ = __add__

    def __mul__(self, other):
        if not isinstance(other, Cyclo):
            other = Cyclo(other)
        return Cyclo(self.a*other.a-self.b*other.b,
                     self.a*other.b+self.b*other.a-self.b*other.b)

    __rmul__ = __mul__

    def bar(self):
        return Cyclo(self.a-self.b, -self.b)

    def re(self):
        return self.a-self.b/2

    def norm(self):
        return self.a**2-self.a*self.b+self.b**2

    def __pow__(self, exponent):
        result, factor = Cyclo(1), self
        while exponent:
            if exponent & 1:
                result = result*factor
            exponent //= 2
            factor = factor*factor
        return result


omega = Cyclo(0, 1)


def coefficients(weights, remainder, t):
    """The scaled quadratic, cubic, quartic coefficients eta*(A,B,C).
    Weights are probabilities on the four possible owners, with fixed long sources.
    """
    z = Cyclo(1-t, t)
    eta = z.norm()
    positions = [omega**s*(z if s < remainder else 1) for s in range(4)]
    owner_phases = [omega.bar()*a*z.bar() for a in positions]  # eta * b_o
    A, B, C = F(), Cyclo(), F()
    for o, weight in enumerate(weights):
        others = [v for i,v in enumerate(positions) if i != o]
        b = owner_phases[o]
        pairs = list(combinations(others, 2))
        pair_re = sum((a*c.bar()).re() for a,c in pairs)
        A += weight*(-16*eta*pair_re + 2*sum((b*c.bar()).re() for c in others))
        triple = others[0]*others[1]*others[2]
        B += 8*weight*(eta*triple + b*sum((a*c for a,c in pairs), Cyclo()))
        C -= 4*weight*sum((b*others[i]*others[(i+1)%3].bar()*
                            others[(i+2)%3].bar()).re() for i in range(3))
    return eta, A, B, C


def scalar_polynomials(weights, r, t):
    eta, A, B, C = coefficients(weights, r, t)
    return A-eta, (A-eta)**2-B.norm(), C


def bernstein(values):
    """Exact Bernstein coefficients from values at i/d, 0 <= i <= d."""
    d = len(values)-1
    powers = [F(0)]*(d+1)
    basis = [F(1)]
    diffs = list(values)
    for k in range(d+1):
        for i,value in enumerate(basis):
            powers[i] += diffs[0]*value
        if k == d:
            break
        diffs = [diffs[i+1]-diffs[i] for i in range(len(diffs)-1)]
        nxt = [F(0)]*(k+2)
        for i,value in enumerate(basis):
            nxt[i] -= value*k/(k+1)
            nxt[i+1] += value*d/(k+1)
        basis = nxt
    result = [sum(powers[k]*F(comb(i,k),comb(d,k)) for k in range(i+1))
              for i in range(d+1)]
    for i, value in enumerate(values):
        x = F(i,d)
        assert value == sum(b*comb(d,j)*x**j*(1-x)**(d-j) for j,b in enumerate(result))
    return result


def get_weights(m,r):
    if m is None:
        return [F(1,4)]*4
    return [F(m+int(s<r),4*m+r) for s in range(4)]


def quarter_certificate():
    d = 10  # A, C, B are degree <=5 after multiplication by eta.
    records = []
    for r in range(4):
        for m in [1, None]:
            weights = get_weights(m,r)
            values = [scalar_polynomials(weights,r,F(i,2*d)) for i in range(d+1)]
            mins = [min(bernstein(coord)) for coord in zip(*values)]
            assert min(mins) >= 0, (r, m, mins)
            records.append((r,m,mins))
    return records


def conditional_deficit(n, t):
    m,r = divmod(n,4)
    assert m >= 1
    eta,A,B,C = coefficients(get_weights(m,r),r,t)
    y = Cyclo(1-t,t)**m
    return (y.norm()*A + (B*(y**3)).re() + C*y.norm()**2)/(54*eta)


def direct_deficit(n):
    total = 0
    for perm in permutations(range(n)):
        a = list(perm)
        for gap in (4,3):
            for off in range(gap):
                a[off::gap] = sorted(a[off::gap])
        total += sum(a[i] > a[j] for i in range(n) for j in range(i+1,n))
    return F(16*n,27)-F(total,factorial(n))


def finite_checks():
    for n in range(1,9):
        direct = direct_deficit(n)
        if n >= 4:
            d = n-1
            nodal = [conditional_deficit(n,F(i,d)) for i in range(d+1)]
            analytic = n*sum(bernstein(nodal))/F(d+1)
            assert direct == analytic
        assert direct > 0
        print(f"n={n}: direct signed deficit = {direct}")


if __name__ == '__main__':
    print("r, owner weights, minima of three degree-10 Bernstein coefficient lists:")
    for r,m,mins in quarter_certificate():
        print(r, 'uniform' if m is None else 'one row', *(str(q) for q in mins))
    finite_checks()
