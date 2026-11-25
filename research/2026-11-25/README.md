# Comparison error from consecutive rank buckets

Miaozhen Yu · 25 November 2026

Consider distinct ranks $0,\ldots,n-1$ and a predetermined word of $p\ge1$ gaps in $[1,n]$. Each pass uses ordinary linear insertion without a sentinel. A successful shift moves one larger key by one chain slot. Key comparisons include a failed stopping comparison whenever one occurs. Repeated or increasing gaps are allowed. The pointwise estimates below apply to every permutation. The exact mean computation uses the uniform law on all $n!$ original permutations. J1–J7 are local labels for this research note. The multistep application and its two counterexamples are in [P03](https://github.com/EternalYMZ/Four-pass-Shellsort-bounds/blob/main/research/2026-11-25/README.md).

The joint-threshold representation follows R09. The exact threshold evolution and its contraction come from R11. Here they control the complete comparison count, including the stopping term. [Earlier rounds and their scopes](https://github.com/EternalYMZ/Project-S/blob/2a6361e542e9a34018736fd831a43cc52f2fcfb0/research/2026-11-25/subsorting.md)

## J1. What a color proxy counts

For each chain $y_0,\ldots,y_{L-1}$ entering a pass, put $m_j=\min_{i<j}y_i$. Insertion past its larger predecessors gives one shift for each inversion. An insertion stops on a key comparison exactly when some predecessor is smaller. Thus its chain comparison count is

$$
\sum_{i<j}\mathbf 1_{y_i>y_j}+\sum_{j=1}^{L-1}\mathbf 1_{y_j>m_j}.
$$

The actual stopping opponent is the greatest smaller predecessor. The minimum only witnesses its existence. Divide the ranks into consecutive nonempty buckets of size at most $b$, let $\phi$ give the bucket label, and define $f_h$ on a color state by the same strict inequalities summed over $h$-chains. Monotonicity gives $\phi(S_hx)=S_h\phi(x)$ on every input. Write $U_h(x)$ for the number of unordered position pairs on the same chain and in the same bucket. Then

$$
0\le C_h(x)-f_h(\phi(x))\le U_h(x)\le B_0,\qquad
B_0=\sum_B\binom{|B|}{2}\le n(b-1)/2 .
$$

Each omitted inversion is a decreasing same-bucket pair. Each omitted stop uses an increasing same-bucket pair formed by the current key and its prefix minimum. Such stops have distinct right endpoints. This injects all omissions together into the pairs counted by $U_h$. For the sorted chain $(0,1,2)$ with buckets $\{0\},\{1,2\}$, the proxy counts two and the actual trace has one cross-bucket comparison. For $(2,1,0)$ with buckets $\{0,1\},\{2\}$ the proxy is two, while insertion on the repeated labels compares three times.

## J2. Bounding the bucket error from the true entrance state

Set $\delta_i=x_i-i$, $F=\sum_i|\delta_i|$, $Q=\sum_i\delta_i^2$. If $i,j=i+kh$ share a bucket of size $m$, then $(\delta_i)_++(-\delta_j)_+\ge kh-m+1$. For $k\le\lfloor(m-1)/h\rfloor$, there are at most $m$ such pairs per bucket and offset. At every larger offset, charge a pair to an endpoint whose signed displacement is at least $(kh-m+1)/2$. A positive displacement can be charged only as a left endpoint, a negative one only as a right endpoint, at most once per offset. With $B(x_i)$ the bucket of $x_i$, this gives

$$
U_h(x)\le\sum_i\left\lfloor\frac{2|\delta_i|+|B(x_i)|-1}{h}\right\rfloor
\le\frac{2F+2B_0}{h}.
$$

For $h\ge b$, square the signed-displacement inequality and use $(a+b)^2\le2(a^2+b^2)$. At each offset the positive left and negative right squares together sum to at most $Q$. Hence

$$
U_h(x)\le 2Q\sum_{k=1}^{\lfloor(n-1)/h\rfloor}(kh-b+1)^{-2}.
$$

If $h\ge2b$, use $kh-b+1\ge(k-\tfrac12)h$ and the half-integer inverse-square sum $\pi^2/2$ to obtain $U_h\le\pi^2Q/h^2$. These bounds may be combined by taking the minimum with $B_0$. The factor in the linear estimate matters. For $x=(0,3,6,1,4,7,2,5,8)$ and $h=b=3$ one has $U_h=9$, $F=16$, $B_0=9$, so $U_h>(F+B_0)/h$.

## J3. Sensitivity of the full proxy

For integer color states define $D(z,w)=\sum_i|z_i-w_i|$ and $\lambda_h=\lceil n/h\rceil-1$. Then

$$
D(S_hz,S_hw)\le D(z,w),\qquad |f_h(z)-f_h(w)|\le\lambda_h D(z,w).
$$

The distance is the sum of Hamming distances over color thresholds. On each chain sorting turns a threshold into a contiguous block, so its Hamming distance becomes the absolute difference of the two counts and cannot increase. Ordinary Hamming distance on color labels can grow, as sorting $(0,1,2)$ and $(3,1,2)$ shows.

To bound the cost change, raise one color at chain index $k$ (starting from zero). At a later index the affected inversion can increase by one and the affected stop can decrease by one, with net change of magnitude at most one. At $k$ at most $k$ inversions disappear and at most one stop is added; for $k=0$ both changes vanish. A chain of length $L$ therefore changes cost by at most $L-1$. Chaining single-coordinate edits gives the estimate. Raising the first color of an all-zero longest chain to one attains $\lambda_h$ on the full color space.

## J5. Exact means from two thresholds

Build a binary interval tree with the buckets as leaves. Every ordered pair of ranks $A>B$ in distinct buckets has one split $[l,m),[m,u)$ separating them. With $\chi_v(t)=\mathbf1_{v<t}$ its contribution is
$(\chi_A(u)-\chi_A(m))(\chi_B(m)-\chi_B(l))$. For a stopping term use the current key and the prefix minimum. The latter lies below a threshold if any earlier key does. Thus each expanded term needs two complete threshold configurations of the **same** permutation. For example, after $S_2$ on four uniform ranks the inversion probabilities at positions $(0,1)$ and $(0,2)$ are $1/2$ and $0$. Independent draws from the correct position marginals instead give $11/36$ and $1/36$. Neither error sign follows from matching marginals.

For thresholds $s\le t$, assign three colors with totals $T=(s,t-s,n-t)$. For first-gap chain lengths $L_j$ and feasible per-chain counts $(a_j,b_j,c_j)$, the probability of that count vector is
$\prod_j\binom{L_j}{a_j,b_j,c_j}/\binom{n}{T_1,T_2,T_3}$. The sorted colors in each chain are fixed by these counts. Propagating each state deterministically through the suffix yields the exact proxy means. The original first-pass cost is computed separately. Its expected shifts and comparisons per chain are $L(L-1)/4$ and $L(L-1)/4+L-H_L$, respectively, because the $j$th key is a record minimum with probability $1/j$.

For $K$ buckets the tree uses $O(K)$ threshold pairs. A crude bound on the number of first-pass states per pair is $D_1=\prod_j\binom{L_j+2}{2}$. The computation can use $O(n+KpnD_1)$ arithmetic operations, with big-integer costs additional. The analyzer uses the exact color law and charges at most $(p-1)B_0$ for omissions after its exact first pass. At $b=1$ the interval collapses. On $n=6$, gaps $(5,3,1)$, the means are $143/30$ shifts and $173/15$ comparisons. The comparison intervals for bucket widths $1,2,3$ are respectively $[173/15,173/15]$, $[413/45,683/45]$ and $[139/20,379/20]$, with 175, 99 and 43 feasible states counted across threshold pairs.

## Reproduce the finite checks

Run from this directory with Python 3 and its standard library.

~~~sh
python verify_joint_framework.py
python verify_transport_strengthened.py
python analyze_gap_word.py --n 6 --gaps 5,3,1 --bucket-width 2 --verify-permutations
~~~

The two verifiers replayed 84,989 tree tests, 40,319 direct insertion passes, 395,649 bucket tests, 241,639 strengthened square-sum tests, 282,120 single-coordinate changes, 1,759,254 state-pair/gap checks and 1,197,855 multistep state-pair checks. The three-color enumeration agrees with permutation means on 66 configurations covering 247 passes. Each of the three displayed examples was compared with all 720 permutations. The proofs above address general sizes. This analytical addition leaves the [existing Lean statement index](../../Shellsort.lean) and the separate Janson–Knuth error question at their previously documented scope.
