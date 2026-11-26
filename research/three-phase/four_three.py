"""Exact Fourier reduction for the last-pass expected deficit with h=4, g=3."""
from fractions import Fraction as Q
from itertools import product
from math import comb
from functools import cache
from collections import defaultdict


def plus(x,y):
    return x[0]+y[0], x[1]+y[1]


def times(x,y):
    """Multiply in Q[omega], omega^2 + omega + 1 = 0."""
    a,b=x
    c,d=y
    return a*c-b*d,a*d+b*c-b*d


def scale(x,a):
    return x[0]*a,x[1]*a


def power(z,k):
    value=(1,0)
    for _ in range(k):value=times(value,z)
    return value


def omega(k):
    return ((1,0),(0,1),(-1,-1))[k%3]


def conjugate(x):
    return x[0]-x[1],-x[1]


def real(x):
    return Q(x[0])-Q(x[1],2)


points=list(product(range(3),repeat=4))


@cache
def coefficient(owner,k,degree=None):
    """Minus 1/2 times the Fourier coefficient including the initial phases."""
    response=(0,0)
    for z in points:
        b=sum(z[j]==(z[owner]+1)%3 for j in range(4) if j!=owner)
        a=sum(z[j]==z[owner] for j in range(4) if j!=owner)
        char=omega(sum(k[i]*(i-z[i]) for i in range(4)))
        reward=(abs(a-1)+abs(b-1) if degree is None else comb(a,degree)+comb(b,degree))
        response=plus(response,scale(char,reward))
    return scale(response,-Q(1,2*len(points)))


def symmetric_polynomial(coeff,d):
    """Write the even-in-x part of Re(coeff A^d) as a polynomial in B.
    x=2t-1, A=((1+omega)+(omega-1)x)/2, x^2=(4B-1)/3."""
    out=defaultdict(Q)
    for j in range(d//2+1):
        v=times(power((Q(1,2),Q(1,2)),d-2*j),power((-Q(1,2),Q(1,2)),2*j))
        c=real(times(coeff,v))*comb(d,2*j)/3**j
        for e in range(j+1):
            out[e]+=c*comb(j,e)*4**e*(-1)**(j-e)
    return out


def reduce_fourier(r,degree=None):
    """n=4m+r. Return coefficient pairs (constant, linear) for each term.

    Key ('I',k,j) represents I_(km+j).  Key ('R',k,j) represents 1/(km+j).
    """
    out=defaultdict(lambda:[Q(0),Q(0)])
    for k in points:
        pos=k.count(1);neg=k.count(2)
        if not pos+neg or (pos-neg)%3:continue
        for owner in range(4):
            c=coefficient(owner,k,degree)
            dp=sum(i<r for i in range(4) if k[i]==1)-(k[owner]==1)
            dm=sum(i<r for i in range(4) if k[i]==2)-(k[owner]==2)
            if not neg or not pos:
                d=dp if pos else dm
                if not pos:c=conjugate(c)
                # Integral of A^(3m+d), since omega^3=1.
                fact= ((0,0),(1,0),(1,1))[(d+1)%3]
                add={('R',3,d+1):real(times(c,fact))}
            else:
                assert pos==neg
                if dp<dm:c=conjugate(c)
                poly=symmetric_polynomial(c,abs(dp-dm))
                add={('I',pos,min(dp,dm)+i):v for i,v in poly.items()}
            for key,coef in add.items():
                out[key][0]+=int(owner<r)*coef
                out[key][1]+=coef
    return {k:tuple(v) for k,v in sorted(out.items()) if any(v)}


@cache
def I(k):
    if k==0:return Q(1)
    return (1+Q(k,2)*I(k-1))/(2*k+1)


def deficit(m,r):
    out=Q(0)
    for (tag,k,j),(a,b) in reduce_fourier(r).items():
        w=a+b*m
        if tag=='I':out+=w*I(k*m+j)
        else:out+=w/Q(k*m+j)
    return out


if __name__=='__main__':
    for r in range(4):
        print('r =',r)
        for key,(a,b) in reduce_fourier(r).items():print(key,' ',a,' + ', b,'m')
        print([float(deficit(m,r)) for m in (1,2,10,50)])
