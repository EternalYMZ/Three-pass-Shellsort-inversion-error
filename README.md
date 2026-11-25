# Project S · P02 · Three-pass Shellsort inversion error

Miaozhen Yu (俞缪臻) · [Project S directory](https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/main/PROJECT-S.md)

For positive coprime gaps, two deterministic identities connect the actual final insertion cost with tagged arc discrepancies. These are interfaces for the analytical error estimate. The Janson–Knuth mean-error bound and its one-sided refinement are outside the formal scope of this snapshot.

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
