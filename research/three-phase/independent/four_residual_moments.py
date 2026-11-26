"""Independent Fourier audit for the four residual sources with lengths (m+1,m+1,m,m).
Output is the integrated reference minus the true sum, weighted by source lengths.
"""
from fractions import Fraction as F
from math import comb
from itertools import combinations
import triple_sign_certificate as ts


def lagrange_power(pts, vals):
    out=[F(0) for _ in pts]
    for i,(x,v) in enumerate(zip(pts,vals)):
        basis=[F(1)]; den=1
        for j,y in enumerate(pts):
            if i==j:continue
            den*=x-y;nxt=[F(0)]*(len(basis)+1)
            for k,a in enumerate(basis):
                nxt[k]-=y*a;nxt[k+1]+=a
            basis=nxt
        for k,a in enumerate(basis):out[k]+=v*a/den
    return out


def moment_score(j):
    def score(h):
        assert h==4
        return [sum(comb(l+b,j)*comb(q,l)*(-1)**(q-l)*comb(3-q,b)*2**(3-q-b)
                    for l in range(q+1) for b in range(4-q)) for q in range(4)]+[0]
    return score


def radial_coefficients(j,m):
    ts.score=moment_score(j)
    def val(k,t):
        num,den=t.numerator,t.denominator
        V=ts.nodal_polynomials(4,2,num,den)
        v=[p.get((k,k),ts.ZERO) for p in V]
        tup=ts.add(v[0],ts.scale(v[1],m-1));assert tup[1]==0
        return F(tup[0],54*den**6)
    result=[]
    for k in (1,2):
        pts=[F(0),F(1,4),F(1,2)]
        B=lambda t:1-3*t*(1-t)
        f=lambda t:(val(k,t)+val(k,1-t))/2
        coefficients=lagrange_power(list(map(B,pts)),list(map(f,pts)))
        for i in range(7):
            t=F(i,6)
            assert f(t)==sum(v*B(t)**s for s,v in enumerate(coefficients))
        result.append(coefficients)
    return result


def holomorphic_coefficients(j,m):
    L=moment_score(j)(4)
    # C_30 / B. U_s=omega^s*a^(s<2); b_o/U_o=omega^{-1}/a.
    out={}
    for o in range(4):
        weight=m+(o<2)
        for pair in combinations([i for i in range(4) if i!=o],2):
            e=(o<2)+sum(i<2 for i in pair)-1
            phase=(o+sum(pair)-1)%3
            out[e]=ts.add(out.get(e,ts.ZERO),ts.scale(ts.ROOTS[phase],weight*L[2]))
        oth=[i for i in range(4) if i!=o]; e=sum(i<2 for i in oth)
        out[e]=ts.add(out.get(e,ts.ZERO),ts.scale(ts.ROOTS[sum(oth)%3],-2*weight*L[3]))
    # Integrating 2*Re(C_30 a^(3m))/(54*B) yields coeff[e]/(3m+e+1).
    result={}
    for e,v in out.items():
        if v==ts.ZERO:continue
        # (omega^(e+1)-1)/(omega-1); e>=-1, explicitly rational in omega.
        geom=ts.ZERO
        for s in range(e+1):geom=ts.add(geom,ts.ROOTS[s%3])
        z=ts.mul(v,geom)
        result[e]=F(2*z[0]-z[1],54)
    return {e:v for e,v in result.items() if v}


def phi(k):return sum((F(comb(k,i)*(-3)**i, (2*i+1)*comb(2*i,i)) for i in range(k+1)),F())
def integrated(j,m):
    P,Q=radial_coefficients(j,m);H=holomorphic_coefficients(j,m)
    return (sum(v*phi(m-1+i) for i,v in enumerate(P) if v)
          + sum(v*phi(2*m-1+i) for i,v in enumerate(Q) if v)
          + sum(v/(3*m+1+i) for i,v in H.items()))


def exact_formula(j,m):
    I=phi
    if j==1:return m*I(m-1)/3+(m+3)*I(m)/6
    if j==2:return 2*m*I(m-1)/9+(5*m+6)*I(m)/9+2*m*I(m+1)/9
    T=F(m,27)*I(m-1)+F(m+1,6)*I(m)+F(2*m,27)*I(m+1)
    return (T-F(m,27)*(I(2*m-1)-I(2*m))-I(2*m)/18-F(1,27)
             +F(m,27*(3*m+2)))


if __name__=='__main__':
    for j in (1,2,3):
        for m in (0,1):
            print(f"j={j} m-weight={m}: radial={radial_coefficients(j,m)}, holomorphic={holomorphic_coefficients(j,m)}")
        for m in range(32):
            a=integrated(j,m);b=exact_formula(j,m)
            assert a==b,(j,m,a,b)
    print('All formulas match for m=0,...,31; displayed coefficient pairs determine every m.')
