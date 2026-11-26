# Project S · P02 · Three-pass Shellsort inversion error

Miaozhen Yu (俞缪臻) · [Project S directory](https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/main/PROJECT-S.md)

This repository contains the tagged-arc identities for the actual last pass, the rank-bucket analysis and specialist parity checks. The analytical proof of the first Janson–Knuth error conjecture and the global optimization of the three-pass gaps are now presented together in P01. Its formal release adds the binomial reference law, finite Bernoulli coupling and conditional transfer to the error of the executed pass. [P01 proof and exact checks](https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/tree/86868d7f2b2ed2271235e357698544dbff7cbea8/audit/inversion-error)

For $g=2$ the deficit $n\psi-\mathbb E M_3$ is nonnegative at all sizes. With odd $h\to\infty$ its scale is $h^{3/2}$, with a coefficient that depends explicitly on $n/h\ge1$. Integer ratios of at least two are strict local minima of the limiting curve. Exact integration agrees with direct insertion on 137,790 permutation/table pairs. [Parity results and verification](research/parity-profile/README.md)

The new research note proves how much ordinary insertion cost can be lost under consecutive rank buckets and how sensitive the complete proxy is to a change in the color state. It includes an exact two-threshold analyzer for any finite predetermined gap word. [Results, derivations and replay scripts](research/2026-11-25/README.md)

## Check the Lean statements

With Git and elan installed, run from the repository root:

```sh
lake exe cache get
lake build
```

[Shellsort.lean](Shellsort.lean) imports the included modules and prints the selected statements and their axioms. Sources and dependency revisions are pinned. Supporting modules may also occur in other paper repositories.

The exact per-input bridge is in [PivotArcCostBridge.lean](Shellsort/PivotArcCostBridge.lean).

## Proof guide

[Read the proof guide](brief.md). The guide explains the mathematical claim and the scope of the Lean results linked above.
