import Shellsort.PivotArcEndpoints
import Shellsort.TaggedArcFluctuation

/-! Identifies the Bernoulli arc reward with the last ordinary insertion
pass on the same permutation, including reindexing by the original slot. -/
noncomputable section
namespace Shellsort
open scoped BigOperators

private theorem arcHits_eq_membership (h g tag ell y z : ℕ)
    (hc : Nat.Coprime h g) (hl : ell < g) :
    arcHits h g ((tag+h*y)%g) ell z =
      if z%g ∈ pivotArcSites h g tag ell y then 1 else 0 := by
  let D := (Finset.range ell).filter (fun w => ((tag+h*y)%g + h*(w+1))%g=z%g)
  have H : arcHits h g ((tag+h*y)%g) ell z = D.card := by
    unfold arcHits D
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_one]
    rfl
  have E : D.Nonempty ↔ z%g ∈ pivotArcSites h g tag ell y := by
    simp [Finset.Nonempty, D, pivotArcSites, Nat.mod_add_mod]
  have le := arcHits_le_one h g ((tag+h*y)%g) ell z hc hl
  rw [H] at le ⊢
  split_ifs with inside
  · have pos := Finset.card_pos.mpr (E.mpr inside)
    omega
  · have emp := Finset.not_nonempty_iff_eq_empty.mp (fun hn => inside (E.mp hn))
    simp [emp]

theorem taggedSubsetArcCount_eq_endpointSum {n : ℕ} (h g ell : ℕ) (hh : 0 < h)
    (hc : Nat.Coprime h g) (hl : ell < g) (i : Fin n) (B : Finset (Fin n)) :
    let owner := i.val % h
    let b := chainLowerCount B h
    let j := (owner+h*b owner)%g
    taggedSubsetArcCount h g ell i B =
      ∑ s ∈ (Finset.range h).erase owner, arcHits h g j ell (s+h*b s) := by
  let owner := i.val%h
  let b := chainLowerCount B h
  let j := (owner+h*b owner)%g
  let f := fun s => if pivotArcHit h g owner ell (b owner) s (b s) then 1 else 0
  have ho : owner ∈ Finset.range h := Finset.mem_range.mpr (Nat.mod_lt _ hh)
  have hz : f owner = 0 := by simp [f, pivotArcHit]
  have erase := Finset.sum_erase_add (Finset.range h) f ho
  rw [hz, Nat.add_zero] at erase
  change (∑ s : Fin h, f s.val) = ∑ s ∈ (Finset.range h).erase owner, arcHits h g j ell (s+h*b s)
  rw [Fin.sum_univ_eq_sum_range, ← erase]
  apply Finset.sum_congr rfl
  intro s hs
  rw [arcHits_eq_membership h g owner ell (b owner) (s+h*b s) hc hl]
  simp [f, pivotArcHit, (Finset.mem_erase.mp hs).1]

/-- Equality for a key tagged by its original slot; in particular the right
side uses the same random variable as the central-variance theorem. -/
theorem twoPass_pivotArc_eq_taggedCount {n : ℕ} (p : RankPlacement n) (h g ell : ℕ)
    (hh : 0 < h) (hg : 0 < g) (hc : Nat.Coprime h g) (hl : ell < g) (i : Fin n) :
    let x := p.symm i
    let j := (gapSort p h x).val % g
    (pivotChainInversions (gapSort (gapSort p h) g) g ((j+h*ell)%g) x : ℝ) =
      |(taggedSubsetArcCount h g ell i (tagLowerState p i).val : ℝ) -
        ((h*ell/g : ℕ) : ℝ)| := by
  have H := twoPass_pivot_arc_endpoint_count p h g ell hh hg hc hl (p.symm i)
  dsimp only at H ⊢
  simp only [Equiv.apply_symm_apply] at H
  rw [gapSort_tag_position p h hh, Equiv.apply_symm_apply, taggedSubsetArcCount_eq_endpointSum
    h g ell hh hc hl i]
  change _ = |((∑ s ∈ (Finset.range h).erase (i.val%h), _ : ℕ) : ℝ) - _|
  exact_mod_cast H

/-- The only hypothesis on the true per-arc cost is a finite central source
variance estimate. The pivot's selected chain may depend on the input. -/
theorem uniform_twoPass_pivotArc_lower_of_sourceVariance {n h : ℕ} (hh : 0 < h)
    (g ell : ℕ) (hg : 0 < g) (hc : Nat.Coprime h g) (hl : ell < g) (i : Fin n)
    (A : ℝ) (hA : 1 ≤ A) (variance : ∀ t : ℝ, 1/4 ≤ t → t ≤ 3/4 →
      let coord := positionChainEquiv n h hh i
      ∀ a, A/768 ≤ sourceArcVariance h g (n/h) (n%h) ell coord.1 t (ownerBitCount coord.2 a)) :
    Real.sqrt A/1600 ≤ uniformAverage (fun p : RankPlacement n =>
      (pivotChainInversions (gapSort (gapSort p h) g) g
         (((gapSort p h (p.symm i)).val%g + h*ell)%g) (p.symm i) : ℝ)) := by
  simp_rw [twoPass_pivotArc_eq_taggedCount _ h g ell hh hg hc hl i]
  exact uniform_pivotArc_abs_lower_of_central_variance hh g ell i _ A hA variance

/-- All the arc rewards add to twice the executed final right shifts. No
probability assumption enters this identity. -/
theorem two_mul_lastCost_eq_sum_taggedArc {n : ℕ} (p : RankPlacement n) (h g : ℕ)
    (hh : 0 < h) (hg : 0 < g) (hc : Nat.Coprime h g) :
    2*(gapInsertionCost (gapSort (gapSort p h) g) 1 (by decide) : ℝ) =
      ∑ i : Fin n, ∑ ell ∈ Finset.range g,
        |(taggedSubsetArcCount h g ell i (tagLowerState p i).val : ℝ) - ((h*ell/g : ℕ) : ℝ)| := by
  let q := gapSort (gapSort p h) g
  have degree := sum_pivotChainInversions_eq_twice_shifts q g hg
  have total : 2*(gapInsertionCost q 1 (by decide) : ℝ) =
      ∑ x : Fin n, ∑ r ∈ Finset.range g, (pivotChainInversions q g r x : ℝ) := by
    exact_mod_cast degree.symm
  rw [total, ← Equiv.sum_comp p.symm (fun x => ∑ r ∈ Finset.range g,
    (pivotChainInversions q g r x : ℝ))]
  apply Finset.sum_congr rfl
  intro i _
  let j := (gapSort p h (p.symm i)).val%g
  symm
  apply Finset.sum_bij (fun ell _ => (j+h*ell)%g)
  · intro ell _; exact Finset.mem_range.mpr (Nat.mod_lt _ hg)
  · intro a ha b hb eq
    have H := (coprime_affine_mod_eq_iff h g j a b hc).mp eq
    simpa [Nat.mod_eq_of_lt (Finset.mem_range.mp ha), Nat.mod_eq_of_lt (Finset.mem_range.mp hb)] using H
  · intro r hr
    obtain ⟨a,ha,eq⟩ := exists_coprime_source_phase h g r j hg hc (Finset.mem_range.mp hr)
    exact ⟨a,Finset.mem_range.mpr ha,eq⟩
  · intro ell hEll
    exact (twoPass_pivotArc_eq_taggedCount p h g ell hh hg hc (Finset.mem_range.mp hEll) i).symm

end Shellsort
end
