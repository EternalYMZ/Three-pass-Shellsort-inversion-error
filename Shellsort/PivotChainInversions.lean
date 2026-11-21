import Shellsort.GapInsertionBridge

/-! The inversions incident to a tagged key and one residue class are counted
in the actual physical array. After sorting that class, both relevant sets
are initial segments, so the absolute difference of their lengths is exact. -/
noncomputable section
namespace Shellsort
open scoped BigOperators

/-- The two genuine orientations of a reversed pair of physical slots. -/
def pivotReversal {n : ℕ} (p : RankPlacement n) (i j : Fin n) : Prop :=
  (i < j ∧ p.symm j < p.symm i) ∨ (j < i ∧ p.symm i < p.symm j)

instance {n : ℕ} (p : RankPlacement n) (i j : Fin n) :
    Decidable (pivotReversal p i j) := by unfold pivotReversal; infer_instance

def pivotChainInversions {n : ℕ} (p : RankPlacement n) (g r : ℕ) (x : Fin n) : ℕ :=
  ((chainPositions n g r).filter (pivotReversal p (p x))).card

/-- In any placement (and even for the pivot's own residue), the mismatch is
precisely the symmetric difference of the smaller-key set and earlier slots. -/
private theorem pivotReversal_iff_mismatch {n : ℕ} (q : RankPlacement n) (x i : Fin n) :
    pivotReversal q (q x) i ↔
      (i < q x ∧ ¬ q.symm i < x) ∨ (q.symm i < x ∧ ¬ i < q x) := by
  unfold pivotReversal
  simp only [Equiv.symm_apply_apply]
  by_cases he : i = q x
  · subst i
    simp
  · have hr : q.symm i ≠ x := fun h => he (by simpa using congrArg q h)
    grind

private theorem nested_mismatch_card {α : Type*} [DecidableEq α] (A B : Finset α)
    (hn : A ⊆ B ∨ B ⊆ A) :
    (((A \ B) ∪ (B \ A)).card : ℤ) = |(A.card : ℤ) - (B.card : ℤ)| := by
  rcases hn with hab | hba
  · have h := Finset.card_le_card hab
    rw [Finset.sdiff_eq_empty_iff_subset.mpr hab, Finset.empty_union,
      Finset.card_sdiff_of_subset hab, Int.natCast_sub h, abs_of_nonpos (by omega)]
    omega
  · have h := Finset.card_le_card hba
    rw [Finset.sdiff_eq_empty_iff_subset.mpr hba, Finset.union_empty,
      Finset.card_sdiff_of_subset hba, Int.natCast_sub h, abs_of_nonneg (by omega)]

/-- When the actual input is sorted on residue r, a pivot's opposite-chain
inversion count is exactly the distance between two prefix sizes. -/
theorem pivotChainInversions_eq_of_sorted {n : ℕ} (q : RankPlacement n) (g r : ℕ)
    (x : Fin n) (hs : ∀ i j, i ∈ chainPositions n g r → j ∈ chainPositions n g r →
      i < j → q.symm i < q.symm j) :
    (pivotChainInversions q g r x : ℤ) =
      |(((chainPositions n g r).filter (fun i => i < q x)).card : ℤ) -
        (chainLowerCount (thresholdSet q x.val) g r : ℤ)| := by
  let C := chainPositions n g r
  let A := C.filter (fun i => i < q x)
  let B := C.filter (fun i => q.symm i < x)
  have hcard : B.card = chainLowerCount (thresholdSet q x.val) g r := by
    congr 1
    ext i
    simp [B, C, chainPositions, thresholdSet, and_comm]
  have hset : C.filter (pivotReversal q (q x)) = (A \ B) ∪ (B \ A) := by
    ext i
    simp only [A, B, Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff,
      pivotReversal_iff_mismatch]
    tauto
  have nested : A ⊆ B ∨ B ⊆ A := by
    by_cases h : A ⊆ B
    · exact Or.inl h
    · obtain ⟨a,ha,hna⟩ := Finset.not_subset.mp h
      have ha' := Finset.mem_filter.mp ha
      have hax : ¬q.symm a < x := fun hl => hna (Finset.mem_filter.mpr ⟨ha'.1,hl⟩)
      right
      intro b hb
      obtain ⟨hbc,hbx⟩ := Finset.mem_filter.mp hb
      refine Finset.mem_filter.mpr ⟨hbc,?_⟩
      by_contra hba
      have hab : a < b := lt_of_lt_of_le ha'.2 (le_of_not_gt hba)
      exact hax (lt_trans (hs a b ha'.1 hbc hab) hbx)
  change ((C.filter (pivotReversal q (q x))).card : ℤ) = _
  rw [hset, nested_mismatch_card A B nested, hcard]

private theorem chain_slots_before_eq {n : ℕ} (g r : ℕ) (j : Fin n) :
    ((chainPositions n g r).filter (fun i => i < j)).card = residuePrefixCount g r j.val := by
  rw [← chainPositions_card]
  let e : {i : Fin n // i.val % g = r ∧ i < j} ≃ {v : Fin j.val // v.val % g = r} :=
    { toFun := fun i => ⟨⟨i.val.val, i.property.2⟩,i.property.1⟩
      invFun := fun v => ⟨⟨v.val.val, lt_trans v.val.isLt j.isLt⟩,v.property,v.val.isLt⟩
      left_inv := by intro i; rfl
      right_inv := by intro v; rfl }
  simpa [chainPositions, Finset.filter_filter, Fintype.card_subtype] using Fintype.card_congr e

/-- After the actual g-sort, both counts are computed on its input. The
indicator is the finite boundary correction for an earlier residue. -/
theorem gapSort_pivotChainInversions {n : ℕ} (p : RankPlacement n) (g r : ℕ)
    (hg : 0 < g) (hr : r < g) (x : Fin n) :
    let j := (p x).val % g
    let N := chainLowerCount (thresholdSet p x.val) g
    (pivotChainInversions (gapSort p g) g r x : ℤ) =
      |((N j + if r < j then 1 else 0 : ℕ) : ℤ) - (N r : ℤ)| := by
  dsimp only
  rw [pivotChainInversions_eq_of_sorted, chain_slots_before_eq,
    residuePrefixCount_formula g r _ hg hr, gapSort_threshold_chain_count,
    ← chainOrdinal_eq_div g hg, gapSort_tag_chain_rank, gapSort_preserves_residue]
  intro i j hi hj hij
  have hc : i.val % g = j.val % g := by
    have h₁ : i.val % g = r := by simpa [chainPositions] using hi
    have h₂ : j.val % g = r := by simpa [chainPositions] using hj
    exact h₁.trans h₂.symm
  exact (gapSort_sorted p g ((gapSort p g).symm i) ((gapSort p g).symm j)
    (by simpa using hc)).mp (by simpa using hij)

/-- Both physical passes are applied to the same input. Every quantity on the
right is obtained from the original threshold subset and original pivot slot. -/
theorem twoPass_pivotChainInversions {n : ℕ} (p : RankPlacement n) (h g r : ℕ)
    (hh : 0 < h) (hg : 0 < g) (hr : r < g) (x : Fin n) :
    let B := thresholdSet p x.val
    let s := (p x).val % h
    let j := (s + h * chainLowerCount B h s) % g
    let N := fun a => ∑ s ∈ Finset.range h, sourcePrefixCount h g a s (chainLowerCount B h s)
    (pivotChainInversions (gapSort (gapSort p h) g) g r x : ℤ) =
      |((N j + if r < j then 1 else 0 : ℕ) : ℤ) - (N r : ℤ)| := by
  dsimp only
  rw [gapSort_pivotChainInversions _ _ _ hg hr, gapSort_tag_position p h hh,
    gapSort_threshold_commutes]
  simp only [lowerStep_target_count _ _ _ _ hh]

/-- Summing over all chains counts both endpoints of every actual unit-gap
insertion shift. The identity is pathwise and allows equal pivot/target chains. -/
theorem sum_pivotChainInversions_eq_twice_shifts {n : ℕ} (p : RankPlacement n)
    (g : ℕ) (hg : 0 < g) :
    ∑ x : Fin n, ∑ r ∈ Finset.range g, pivotChainInversions p g r x =
      2 * gapInsertionCost p 1 (by decide) := by
  let V (i j : Fin n) : ℕ := if i < j ∧ p.symm j < p.symm i then 1 else 0
  have inc (i j : Fin n) :
      (if pivotReversal p i j then 1 else 0 : ℕ) = V i j + V j i := by
    unfold pivotReversal V
    split_ifs <;> grind
  have deg (x : Fin n) :
      ∑ r ∈ Finset.range g, pivotChainInversions p g r x =
        ∑ j : Fin n, (V (p x) j + V j (p x)) := by
    let S := Finset.univ.filter (pivotReversal p (p x))
    have hsplit := Finset.card_eq_sum_card_fiberwise (s := S) (t := Finset.range g)
      (f := fun i : Fin n => i.val % g) (by intro i _; exact Finset.mem_range.mpr (Nat.mod_lt _ hg))
    calc
      _ = S.card := by
        rw [hsplit]
        apply Finset.sum_congr rfl
        intro r _
        simp [S, pivotChainInversions, chainPositions, Finset.filter_filter, and_comm]
      _ = ∑ j : Fin n, (if pivotReversal p (p x) j then 1 else 0) := by
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      _ = _ := Finset.sum_congr rfl fun j _ => inc _ j
  simp_rw [deg]
  have reindex := Equiv.sum_comp p (fun i => ∑ j : Fin n, (V i j + V j i))
  rw [reindex, gapInsertionCost_eq_gapInversions, gapInversions_nat_pair_sum]
  simp only [Finset.sum_add_distrib, Nat.mod_one, and_true]
  have rev : (∑ i : Fin n, ∑ j : Fin n, V i j) = ∑ i : Fin n, ∑ j : Fin n, V j i :=
    Finset.sum_comm
  rw [rev]
  dsimp only [V]
  omega

end Shellsort
end
