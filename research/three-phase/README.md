# The second Janson–Knuth conjecture for a gap of three

For ordinary $(h,3,1)$ insertion Shellsort on a uniform permutation, $n\psi(h,3)-\mathbb E M_3$ is strictly positive for every $n\ge1$ and every $h\ge2$ coprime to three. For $h=1$ both quantities vanish. This includes the strictly decreasing schedules and sizes at which a preliminary pass is redundant. [Janson and Knuth, §10](https://arxiv.org/pdf/cs/9608105#page=15)

The proof groups equal-length sources into triples with all three starting phases. For a fixed target, a triple outside the pivot source has total hit probability one, allowing the convex comparison at matched mean. The pivot's own triple is treated with its actual conditional count. Long and short chains can leave four ungrouped sources. Their three factorial moments, weighted by the numbers of available pivot slots, give a positive integrated correction also in this final residue case. The full result is analytical. The programs check its finite coefficient identities by arithmetic in the third roots of unity. [Coefficient generator](four_three.py) · [Factorial moments and independent physical means](check_three_phase.py)

For $(4,3)$ the exact finite deficit has a positive expression at every size and tends to $55/81$. With the gaps in the order $(2,g,1)$, every odd $g\ge3$ also satisfies the strict sign for all $n$. Its fixed-$g$ deficit tends to $(g^2-1)(g^2-5)/(96g)$. These first-gap-two tables use a larger second gap. [Independent exact checks](check_small_gap_sign.py)

Run from this directory with Python 3.9 or newer.

~~~sh
python -B check_three_phase.py
python -B check_small_gap_sign.py
~~~

The first program reproduces the three coefficient dictionaries, compares finite bounds with 160 independently computed means and tests 25,120 size/gap choices. The second compares the formulas with physical sorting on 277,398 permutation/schedule pairs. [Three-phase results](three-phase-results.txt) · [Two-source and four-source results](exact-results.txt)

An independent expansion reproduces the three residual factorial moments. For all 27 coprime first gaps from 2 to 41 it also certifies the stronger conditional inequality at each continuous pivot value when $n\ge h$, after averaging over the physical pivot slot. Conditioning on a discrete rank can reverse the sign for that rank. At $(n,h,g)=(7,4,3)$ the middle key gives $-41/1890$. [Independent moments](independent/four_residual_moments.py) · [Threshold certificate](independent/triple_sign_certificate.py) · [27 exact bounds](independent/thresholds.txt) · [Physical convolution and permutation check](independent/triple_sign_replay.py)
