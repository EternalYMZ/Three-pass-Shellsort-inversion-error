# Counting final-pass inversions from a tagged key

After coprime positive gaps $h,g$, each $g$-chain is sorted. For a tagged key $x$, the smaller keys on another chain form a prefix, as do the slots to its left. The absolute difference of these prefix lengths counts exactly the inversions with $x$ on that chain.

Let $b_s$ count keys smaller than $x$ on source chain $s$. Its marked prefix ends just before slot $s+hb_s$. Record that endpoint modulo $g$. Start at the residue occupied by $x$ after the first pass and follow steps of $h$ modulo $g$. For an arc of length $0\le\ell<g$, let $Q_{x,\ell}$ count the other source-chain endpoints on its visited residues, with multiplicity. Coprimality makes the visited residues distinct. Comparing the two prefix counts telescopes along the arc, leaving the endpoint count and a rounding term. Summing over keys and arcs counts each inversion twice:
$$2M_3=\sum_x\sum_{\ell=0}^{g-1}|Q_{x,\ell}-\lfloor h\ell/g\rfloor|.$$

Lean verifies this identity for each input. Comparing the actual endpoint law with the reference law for the Janson–Knuth mean term $n\psi(h,g)$ requires a further probabilistic argument. The absolute-error estimate has an analytical derivation. The general one-sided inequality without an additive error remains open.

[PivotArcEndpoints.lean](https://github.com/EternalYMZ/Three-pass-Shellsort-inversion-error/blob/afe8a5e00022093474444bc1d3b6aebc3481a940/Shellsort/PivotArcEndpoints.lean) · [PivotArcCostBridge.lean](https://github.com/EternalYMZ/Three-pass-Shellsort-inversion-error/blob/afe8a5e00022093474444bc1d3b6aebc3481a940/Shellsort/PivotArcCostBridge.lean)
