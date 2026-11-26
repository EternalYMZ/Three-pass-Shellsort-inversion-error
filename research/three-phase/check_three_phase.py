"""Check the coefficients and finite lower bounds of the three-phase proof.

The independent physical mean conditions on the uniformly random prefix of a
rank permutation. No Fourier transform or Bernoulli comparison is used there.
Run beside four_three.py with Python 3.9 or newer.
"""
from fractions import Fraction as Q
from functools import cache
from itertools import product
from math import comb,prod
from four_three import reduce_fourier, I


@cache
def mass(trials,j):
    if not 0<=j<=trials:return Q(0)
    return Q(comb(trials,j)*2**(trials-j),3**trials)


@cache
def slope(trials,k):
    return 1-2*sum(mass(trials,j) for j in range(k))


@cache
def reference(h):
    return sum(abs(i-h//3)*mass(h-1,i) for i in range(h))


def check_tables():
    tab={
    1:{('I',1,-1):(0,Q(1,3)),('I',1,0):(Q(1,2),Q(1,6))},
    2:{('I',1,-1):(0,Q(2,9)),('I',1,0):(Q(2,3),Q(5,9)),('I',1,1):(0,Q(2,9)),
       ('R',3,1):(-Q(1,9),-Q(1,3)),('R',3,2):(Q(2,9),Q(1,3))},
    3:{('I',1,-1):(0,Q(1,27)),('I',1,0):(Q(1,6),Q(1,6)),('I',1,1):(0,Q(2,27)),
       ('I',2,-1):(0,-Q(1,27)),('I',2,0):(-Q(1,18),Q(1,27)),
       ('R',3,1):(-Q(1,27),-Q(1,9)),('R',3,2):(0,Q(1,27))}}
    for j,expected in tab.items():assert reduce_fourier(2,j)==expected
    print("Three factorial-moment coefficient dictionaries agree symbolically at every m>=1.")


@cache
def remainder_moments(m):
    if m==0:
        return Q(1,2),Q(2,3),Q(2,27),Q(1,6)
    d1=Q(m,3)*I(m-1)+Q(m+3,6)*I(m)
    d2=Q(2*m,9)*I(m-1)+Q(5*m+6,9)*I(m)+Q(2*m,9)*I(m+1)
    upper=Q(m,27)*I(m-1)+Q(m+1,6)*I(m)+Q(2*m,27)*I(m+1)
    d3=upper-Q(m,27)*(I(2*m-1)-I(2*m))-I(2*m)/18-Q(1,27)+Q(m,27*(3*m+2))
    assert d1>0 and d3<upper and d2>=d1+upper
    return d1,d2,d3,upper


def proof_bound(n,h):
    m,r=divmod(n,h)
    k=h//3
    a=slope(h-3,k)
    b=2*mass(h-3,k-1)
    assert 3*a+2*b>0
    bulk=Q(0)
    for L,count in [(m,(h-r)//3),(m+1,r//3)]:
        if count and L:
            delta=(3*a+b)*I(L-1)/18+b*I(L)/9
            assert delta>0
            bulk+=3*L*count*delta
    if h%3==1:
        if r%3!=2:return bulk
        a,b=slope(h-4,k),2*mass(h-4,k-1)
        d1,d2,d3,upper=remainder_moments(m)
        assert a> -b and d3<upper and d2>=d1+upper
        return bulk+a*d1+b*d2-b*d3/(2*k-1)
    base_slope=slope(h-2,k)
    assert base_slope>0
    if r%3==1:
        paired=I(m)+(Q(m,2)*I(m-1) if m else 0)
        return bulk+base_slope*paired/3
    L=m+int(r%3==2)
    return bulk+(2*L*base_slope*I(L-1)/12 if L else 0)


def physical_mean(n,h):
    lengths=[(n+h-1-s)//h for s in range(h)]
    # Slots occupied by all smaller keys in each target after the h-pass.
    prefixes=[]
    for s,L in enumerate(lengths):
        counts=[0,0,0]
        rows=[]
        for y in range(L+1):
            rows.append((comb(L,y),tuple(counts)))
            counts[(s+h*y)%3]+=1
        prefixes.append(rows)
    nums=[0]*n
    for low in product(*(range(L+1) for L in lengths)):
        q=sum(low)
        if q==n:continue
        weight=1
        ranks=[0,0,0]
        for s,y in enumerate(low):
            times,vec=prefixes[s][y]
            weight*=times
            for j in range(3):ranks[j]+=vec[j]
        incidence=0
        for o,(L,y) in enumerate(zip(lengths,low)):
            if y==L:continue
            j=(o+h*y)%3
            with_pivot=sum(abs(ranks[j]+int(a<j)-ranks[a]) for a in range(3) if a!=j)
            incidence+=(L-y)*with_pivot
        nums[q]+=weight*incidence
    return sum(Q(w,2*(n-q)*comb(n,q)) for q,w in enumerate(nums))


def main():
    check_tables()
    out=total=0
    for h in (4,5,7,8,10,11,13,14,16,17,19):
        sizes=range(1,min(h+5,17)+1)
        for n in sizes:
            true=n*reference(h)-physical_mean(n,h)
            bound=proof_bound(n,h)
            assert true>0 and true>=bound>=0,(n,h,true,bound)
            assert bound>0 or n==1,(n,h,bound)
            total+=1
    print(f"Physical prefix enumeration independently proves the reported lower bound in all {total} finite cases.")
    for h in range(4,124):
        if h%3==0:continue
        for m in (0,1,2,8,20):
            for r in range(h):
                n=m*h+r
                if n==0:continue
                assert proof_bound(n,h)>0 or n==1
                out+=1
    print(f"Checked positive proof bounds or the immediate n=1 case for {out} integer sizes and gap choices.")


if __name__=='__main__':main()
