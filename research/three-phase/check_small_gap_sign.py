"""Reproduce the Fourier certificates for h=2 and (h,g)=(4,3).
Only the standard library is used. Run beside four_three.py.
"""
from fractions import Fraction as Q
from functools import cache
from itertools import permutations
from math import comb, factorial
from four_three import reduce_fourier, I, deficit


def inv(a):
    return sum(x>y for i,x in enumerate(a) for y in a[i+1:])


def gap_sort(a,g):
    b=list(a)
    for i in range(min(g,len(b))):b[i::g]=sorted(b[i::g])
    return b


def phi(g,d):
    """Number of disagreements across a rank cut from an even/odd count difference."""
    r=d%(2*g)
    s=r%g
    v=min(s,g+1-s)
    z=v if r<g else 1-v
    return abs(z-z%2)


def h2_mean(n,g):
    """Independent rational evaluation of the integrated cyclic distance.

    Conditionally Y,Y' ~ iid Bin(m,t).  Integrate the product of two
    binomial probabilities by the beta integral.
    """
    m=n//2
    accum=Q(0)
    for a in range(m+1):
        for b in range(m+1):
            u=(a-b)%g
            distance=min(u,g-u)
            accum+=distance*Q(comb(m,a)*comb(m,b),(2*m+1)*comb(2*m,a+b))
    return (n+1)*accum/2


def four_three_positive(m,r):
    if not m:
        return Q(16*(4*m+r),27)-Q(r*(r-1),4)
    if r==0:
        return Q(m,18)*I(m-1)+Q(8*m,9)*I(m)+Q(4*m,27*(3*m+1))
    if r==1:
        return Q(m,18)*I(m-1)+Q(8*m+4,9)*I(m)+Q(4*(m+1),27*(3*m+1))
    if r==2:
        return (Q(m,27)*I(m-1)+Q(11*m+9,18)*I(m)+Q(8*m,27)*I(m+1)
                +Q(2*m,27)*(I(2*m-1)-I(2*m))+I(2*m)/9
                +Q(4*(m+1),27*(3*m+2)))
    return Q(m+1,18)*I(m)+Q(8*m+4,9)*I(m+1)+Q(4*m,27*(3*m+4))


def verify_fourier_table():
    # 2nd moment entries for r=2 include the two terms combined as a
    # manifestly positive rational fraction in the written display.
    table=[
        {('I',1,-1):(0,Q(1,18)),('I',1,0):(0,Q(8,9)),('R',3,1):(0,Q(4,27))},
        {('I',1,-1):(0,Q(1,18)),('I',1,0):(Q(4,9),Q(8,9)),('R',3,1):(Q(4,27),Q(4,27))},
        {('I',1,-1):(0,Q(1,27)),('I',1,0):(Q(1,2),Q(11,18)),('I',1,1):(0,Q(8,27)),
         ('I',2,-1):(0,Q(2,27)),('I',2,0):(Q(1,9),-Q(2,27)),
         ('R',3,1):(-Q(4,27),-Q(4,9)),('R',3,2):(Q(4,9),Q(16,27))},
        {('I',1,0):(Q(1,18),Q(1,18)),('I',1,1):(Q(4,9),Q(8,9)),('R',3,4):(0,Q(4,27))},
    ]
    for r in range(4):
        assert table[r]==reduce_fourier(r)
        for m in range(1,81):
            assert four_three_positive(m,r)==deficit(m,r)>0
    print("The exact four-source Fourier coefficients agree symbolically in all four size residues.")


def check_distance():
    checks=0
    for g in range(3,42,2):
        for d in range(-2*g,2*g+1):
            r=d%g
            assert phi(g,d)==phi(g,1-d)==phi(g,d+g)
            assert phi(g,d)+phi(g,-d)==2*min(r,g-r)
            checks+=1
    print(f"Checked invariance and symmetrization of {checks} integer folded-threshold states.")
    count=0
    for n in range(1,22):
        for g in range(3,24,2):
            actual=h2_mean(n,g)
            assert actual<n*Q(g*g-1,8*g)
            count+=1
    print(f"All {count} independently integrated h=2 finite means have strictly positive deficit.")


def check_insertion():
    checks=0
    for n in range(1,9):
        words=[(4,3)]+[(2,g) for g in range(3,12,2)]
        totals={p:0 for p in words}
        for a in permutations(range(n)):
            first={h:gap_sort(a,h) for h,_ in words}
            for h,g in words:
                totals[h,g]+=inv(gap_sort(first[h],g))
                checks+=1
        for (h,g),total in totals.items():
            physical=Q(total,factorial(n))
            if h==2:assert physical==h2_mean(n,g)
            else:
                m,r=divmod(n,h)
                assert physical==Q(16*n,27)-four_three_positive(m,r)
    print(f"Ordinary rank execution agrees in all {checks} permutation/word comparisons for n<=8.")


if __name__=='__main__':
    verify_fourier_table()
    check_distance()
    check_insertion()
    for n in (4,5,6,7,8,15,20,60,100):
        d=four_three_positive(*divmod(n,4))
        print(f"n={n:3d}, h=4, g=3: deficit={float(d):.12f}, exact={d}")
