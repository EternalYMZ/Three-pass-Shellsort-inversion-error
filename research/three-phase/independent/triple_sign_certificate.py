"""Uniform threshold-sign certificates for (h,3) using exact Bernstein arithmetic.

Usage: python triple_sign_certificate.py 4 5 7 8
For each certified h coprime to 3, every threshold is covered for every n >= h.
Shorter lengths are compared exactly after their sole nonidentity presort.
"""
from fractions import Fraction
from functools import cache
from math import comb, gcd, isqrt, lcm
from sys import argv

ZERO=(0,0)
ONE=(1,0)
ROOTS=[ONE,(0,1),(-1,-1)]

def add(a,b):
    return a[0]+b[0],a[1]+b[1]

def sub(a,b):
    return a[0]-b[0],a[1]-b[1]

def mul(a,b):
    return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]-a[1]*b[1]

def bar(a):
    return a[0]-a[1],-a[1]

def scale(a,b):
    return a[0]*b,a[1]*b

def norm(a):
    return a[0]*a[0]-a[0]*a[1]+a[1]*a[1]

def ceil_norm(a):
    n=norm(a)
    q=isqrt(n)
    return q+(q*q<n)


@cache
def score(h):
    N=h-1
    out=[]
    for k in range(N+1):
        val=0
        for l in range(k+1):
            for b in range(N-k+1):
                val+=abs(l+b-h//3)*comb(k,l)*(-1)**(k-l)*comb(N-k,b)*2**(N-k-b)
        out.append(val)
    return out+[0]


@cache
def t_transform(d):
    # Invert interpolation on 0,1/d,...,1. Coefficients below are for t=x/2.
    columns=[]
    for k in range(d+1):
        prod=[1]
        denominator=1
        for j in range(d+1):
            if j==k:
                continue
            nxt=[0]*(len(prod)+1)
            for i,v in enumerate(prod):
                nxt[i]-=j*v
                nxt[i+1]+=d*v
            prod=nxt
            denominator*=k-j
        columns.append([sum(Fraction(prod[j]*comb(i,j),denominator*comb(d,j))
                             for j in range(i+1)) for i in range(d+1)])
    common=lcm(*(f.denominator for col in columns for f in col))
    mat=[[int(columns[k][i]*common) for k in range(d+1)] for i in range(d+1)]
    # Polynomial reproduction checks the entire change-of-basis matrix.
    for i,row in enumerate(mat):
        for k in range(d+1):
            val=sum(V*j**k for j,V in enumerate(row))
            assert val*comb(d,k)==(common*d**k*comb(i,k) if i>=k else 0)
    return mat,common


@cache
def u_transform(d):
    den=lcm(*(comb(d,i) for i in range(d+1)))
    return [[comb(j,k)*(den//comb(d,k)) for k in range(j+1)] for j in range(d+1)], den


def nodal_polynomials(h,r,num,den):
    # Return rho-independent Fourier coefficients at t=num/den for two owner-weight vectors.
    z=add((den-num,0),scale(ROOTS[h%3],num));eta=norm(z)
    a=[mul(ROOTS[s%3],z if s<r else (den,0)) for s in range(h)]
    unique=list(dict.fromkeys(a))
    total={(0,0):ONE}
    for v in a:
        prev=total.copy()
        for (i,j),val in prev.items():
            ix=(i+1,j);total[ix]=add(total.get(ix,ZERO),mul(v,val))
            ix=(i,j+1);total[ix]=add(total.get(ix,ZERO),mul(bar(v),val))
    res=[{},{}];L=score(h)
    for v in unique:
        # Divide the bivariate product by the owner's linear factor.
        S={}
        for q in range(h):
            for i in range(q+1):
                j=q-i
                S[i,j]=sub(total[i,j],add(mul(v,S.get((i-1,j),ZERO)),mul(bar(v),S.get((i,j-1),ZERO))))
        vb=mul(mul(ROOTS[-h%3],v),bar(z))
        ws=[sum(1+(idx<r) for idx,xx in enumerate(a) if xx==v),a.count(v)]
        for q in range(2,h+1):
            for j in range(q//2+1):
                i=q-j
                if (i-j)%3:
                    continue
                w=sub(scale(add(mul(vb,S.get((i-1,j),ZERO)),mul(bar(vb),S.get((i,j-1),ZERO))),den*L[q-1]),
                      scale(S.get((i,j),ZERO),2*eta*L[q]))
                for k,wt in enumerate(ws):
                    if wt:
                        res[k][i,j]=add(res[k].get((i,j),ZERO),scale(w,wt*den**(h-q)))
    return res


def controls(h,r):
    dt=h+2; den=2*dt;du=h//2-1
    T,tden=t_transform(dt)
    U,uden=u_transform(du)
    data=[nodal_polynomials(h,r,x,den) for x in range(dt+1)]
    reports=[]
    for k,wsum in enumerate((h+r,h)):
        # Project radial and angular Fourier components first to Bernstein basis in u=|y|^2.
        planes=[]
        for V in data:
            components=[[ZERO for j in range(du+1)] for l in range(h//3+1)]
            for (i,j),v in V[k].items():
                if i==j:
                    assert v[1]==0
                    components[0][j-1]=v
                else:
                    components[(i-j)//3][j]=scale(v,2)
            planes.append([[tuple(sum(row[n]*comp[n][e] for n in range(len(row))) for e in (0,1))
                            for comp in components] for row in U])
        minimum=None
        for row in T:
            for j in range(du+1):
                C=[tuple(sum(a*planes[x][j][l][e] for x,a in enumerate(row)) for e in (0,1)) for l in range(h//3+1)]
                balance=C[0][0]-sum(ceil_norm(z) for z in C[1:])
                minimum=balance if minimum is None else min(balance,minimum)
        reports.append(Fraction(minimum, 2*3**(h-1)*wsum*den**(h+2)*uden*tden))
    return reports


def certificate(h):
    assert h>=2 and gcd(h,3)==1
    rows=[controls(h,r) for r in range(h)]
    cert=min(min(row) for row in rows)
    assert cert>0,(h,cert)
    # eta=|1-t+t*omega^h|^2<=1, so cert is also a gap in true per-key reward.
    return cert



def psi(h):
    N=h-1
    return Fraction(sum(abs(k-h//3)*comb(N,k)*2**(N-k) for k in range(N+1)),3**N)


@cache
def single_pass_three(n):
    """When n<h the first pass is the identity. Use a binary merge of each pair of chains."""
    lengths=[len(range(j,n,3)) for j in range(3)]
    result=Fraction()
    for j,a in enumerate(lengths):
        for b in lengths[j+1:]:
            for i in range(1,a+b):
                total=sum(abs(x-(i+1)//2)*comb(a,x)*comb(b,i-x)
                          for x in range(max(0,i-b),min(a,i)+1))
                result+=Fraction(total,comb(a+b,i))
    return result


def boundary_constant(h):
    """The exact integral of the limiting Poisson boundary layer."""
    coeffs=nodal_polynomials(h,0,0,1)[1]
    root=ROOTS[h%3]
    result=Fraction()
    for (i,j),val in coeffs.items():
        denom=sub((i+j,0),add(scale(root,i),scale(bar(root),j)))
        numer=mul(val,bar(denom))
        result+=(1 if i==j else 2)*Fraction(2*numer[0]-numer[1],2*norm(denom))
    return result/3**(h-1)
if __name__=='__main__':
    for h in map(int,argv[1:] or [4,5,7,8]):
        gap=certificate(h)
        assert all(n*psi(h)>single_pass_three(n) for n in range(1,h))
        print(f"h={h}: n>=h threshold gap {gap}; " +
              f"short-n gap {min(n*psi(h)-single_pass_three(n) for n in range(1,h))}; " +
              f"boundary constant {boundary_constant(h)}",flush=True)
