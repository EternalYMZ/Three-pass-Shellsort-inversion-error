import Shellsort.PivotChainInversions
import Shellsort.CoprimePhase

/-! An arc on the residue cycle starts just after j and ends at j+h*l.
The source prefix counts telescope to differences of its endpoint indicators. -/
noncomputable section
namespace Shellsort
open scoped BigOperators

def arcHits (h g j l z : ℕ) : ℕ :=
  ∑ w ∈ Finset.range l, if (j + h*(w+1)) % g = z % g then 1 else 0

theorem arcHits_le_one (h g j l z : ℕ) (hc : Nat.Coprime h g) (hl : l < g) :
    arcHits h g j l z ≤ 1 := by
  unfold arcHits
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_one]
  apply Finset.card_le_one.mpr
  intro u hu v hv
  obtain ⟨hu₁,hu₂⟩ := Finset.mem_filter.mp hu
  obtain ⟨hv₁,hv₂⟩ := Finset.mem_filter.mp hv
  have hm := (coprime_affine_mod_eq_iff h g j (u+1) (v+1) hc).mp (hu₂.trans hv₂.symm)
  have hu' := Finset.mem_range.mp hu₁
  have hv' := Finset.mem_range.mp hv₁
  rw [Nat.mod_eq_of_lt (by omega : u+1 < g), Nat.mod_eq_of_lt (by omega : v+1 < g)] at hm
  omega

theorem arcHits_start (h g j l z : ℕ) (hc : Nat.Coprime h g) (hl : l < g)
    (hj : z % g = j % g) : arcHits h g j l z = 0 := by
  apply Finset.sum_eq_zero
  intro w hw
  have hw' := Finset.mem_range.mp hw
  have hne : (j+h*(w+1)) % g ≠ z % g := by
    intro he
    have hm := (coprime_affine_mod_eq_iff h g j (w+1) 0 hc).mp (by simpa using he.trans hj)
    rw [Nat.mod_eq_of_lt (by omega : w+1 < g)] at hm
    simp at hm
  simp [hne]

private theorem arcHits_step (h g j l z : ℕ) :
    (arcHits h g j l (z+h) : ℤ) - (arcHits h g j l z : ℤ) =
      (if j%g=z%g then (1:ℤ) else 0) - (if (j+h*l)%g=z%g then (1:ℤ) else 0) := by
  induction l with
  | zero => simp [arcHits]
  | succ l ih =>
    have hs : (j+h*(l+1))%g=(z+h)%g ↔ (j+h*l)%g=z%g := by
      rw [Nat.mul_succ, ← Nat.add_assoc]
      constructor
      · exact Nat.ModEq.add_right_cancel' h
      · exact Nat.ModEq.add_right h
    simp only [arcHits, Finset.sum_range_succ, Nat.cast_add, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero, hs] at ih ⊢
    -- The visit to the intermediate residue cancels.
    omega

theorem sourcePrefixCount_arc_difference (h g j l s b : ℕ) :
    (sourcePrefixCount h g (j%g) s b : ℤ) -
      (sourcePrefixCount h g ((j+h*l)%g) s b : ℤ) =
    (arcHits h g j l (s+h*b) : ℤ) - (arcHits h g j l s : ℤ) := by
  induction b with
  | zero => simp [sourcePrefixCount]
  | succ b ih =>
    have hs := arcHits_step h g j l (s+h*b)
    change (_ : ℤ) - _ = _ - _ at hs
    rw [Nat.mul_succ, ← Nat.add_assoc]
    simp only [sourcePrefixCount, Finset.sum_range_succ, Nat.cast_add, Nat.cast_ite,
      Nat.cast_zero, Nat.cast_one] at ih ⊢
    simp only [eq_comm (a := (s+h*b)%g)] 
    omega

private theorem residue_prefix_add_carry (g a b : ℕ) (hg : 0 < g) :
    residuePrefixCount g ((a+b)%g) b + a/g = (a+b)/g := by
  rw [residuePrefixCount_formula _ _ _ hg (Nat.mod_lt _ hg), Nat.add_div hg]
  by_cases carry : g ≤ a%g + b%g
  · have hm := Nat.add_mod_add_of_le_add_mod carry
    have ha := Nat.mod_lt a hg
    split_ifs <;> omega
  · rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega)]
    split_ifs <;> omega

theorem sum_initial_arcHits (h g j l : ℕ) (hg : 0 < g) :
    (∑ s ∈ Finset.range h, arcHits h g j l s) + j/g = (j+h*l)/g := by
  induction l with
  | zero => simp [arcHits]
  | succ l ih =>
    have hs : (∑ s ∈ Finset.range h, if (j+h*(l+1))%g = s%g then 1 else 0) =
        residuePrefixCount g ((j+h*(l+1))%g) h := by simp [residuePrefixCount, eq_comm]
    have carry := residue_prefix_add_carry g (j+h*l) h hg
    rw [Nat.mul_succ, ← Nat.add_assoc] at hs ⊢
    simp only [arcHits, Finset.sum_range_succ, Finset.sum_add_distrib, Nat.mul_succ,
      ← Nat.add_assoc] at ih ⊢
    omega

private theorem sum_initial_arcHits_correction (h g j l : ℕ) (hg : 0 < g) (hj : j < g) :
    (∑ s ∈ Finset.range h, arcHits h g j l s) =
      h*l/g + if (j+h*l)%g < j then 1 else 0 := by
  have init := sum_initial_arcHits h g j l hg
  rw [Nat.div_eq_of_lt hj, Nat.add_zero, Nat.add_div hg, Nat.div_eq_of_lt hj,
    Nat.zero_add, Nat.mod_eq_of_lt hj] at init
  by_cases carry : g ≤ j + (h*l)%g
  · have hc : g ≤ j%g + (h*l)%g := by simpa [Nat.mod_eq_of_lt hj] using carry
    have hm := Nat.add_mod_add_of_le_add_mod hc
    rw [Nat.mod_eq_of_lt hj] at hm
    have hr := Nat.mod_lt (h*l) hg
    split_ifs at init ⊢ <;> omega
  · have hm : (j+h*l)%g = j+(h*l)%g := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt (by omega)]
    split_ifs at init ⊢ <;> omega

/-- Finite arc identity before specialization to a tagged source. The initial
phase count absorbs exactly the earlier-residue correction and floor(h*l/g). -/
theorem sum_source_arc_endpoint_identity (h g j l : ℕ) (hg : 0 < g)
    (hj : j < g) (b : ℕ → ℕ) :
    let r := (j+h*l)%g
    let N := fun a => ∑ s ∈ Finset.range h, sourcePrefixCount h g a s (b s)
    ((N j + if r < j then 1 else 0 : ℕ) : ℤ) - (N r : ℤ) =
      ((∑ s ∈ Finset.range h, arcHits h g j l (s+h*b s) : ℕ) : ℤ) -
        ((h*l/g : ℕ) : ℤ) := by
  dsimp only
  have H := Finset.sum_congr (s₁ := Finset.range h) rfl (fun s _ =>
    sourcePrefixCount_arc_difference h g j l s (b s))
  simp only [Nat.mod_eq_of_lt hj, Finset.sum_sub_distrib, ← Nat.cast_sum] at H
  rw [sum_initial_arcHits_correction h g j l hg hj] at H
  push_cast at H ⊢
  linarith

/-- The true two-pass opposite-chain inversion count is |Q-floor(h*l/g)|.
Q counts endpoints of nonpivot sources in the arc, and each summand is a bit
by arcHits_le_one. This is a pathwise identity for the ordinary placement. -/
theorem twoPass_pivot_arc_endpoint_count {n : ℕ} (p : RankPlacement n) (h g l : ℕ)
    (hh : 0 < h) (hg : 0 < g) (hc : Nat.Coprime h g) (hl : l < g) (x : Fin n) :
    let B := thresholdSet p x.val
    let b := chainLowerCount B h
    let owner := (p x).val % h
    let j := (owner + h*b owner)%g
    let r := (j+h*l)%g
    (pivotChainInversions (gapSort (gapSort p h) g) g r x : ℤ) =
      |((∑ s ∈ (Finset.range h).erase owner, arcHits h g j l (s+h*b s) : ℕ) : ℤ) -
        ((h*l/g : ℕ) : ℤ)| := by
  let B := thresholdSet p x.val
  let b := chainLowerCount B h
  let owner := (p x).val % h
  let j := (owner+h*b owner)%g
  let r := (j+h*l)%g
  have hj : j < g := Nat.mod_lt _ hg
  have howner : owner ∈ Finset.range h := Finset.mem_range.mpr (Nat.mod_lt _ hh)
  have hzero : arcHits h g j l (owner+h*b owner) = 0 := by
    apply arcHits_start _ _ _ _ _ hc hl
    exact (Nat.mod_eq_of_lt hj).symm
  have erase := Finset.sum_erase_add (Finset.range h) (fun s => arcHits h g j l (s+h*b s)) howner
  rw [hzero, Nat.add_zero] at erase
  change (pivotChainInversions (gapSort (gapSort p h) g) g r x : ℤ) = _
  rw [twoPass_pivotChainInversions p h g r hh hg (Nat.mod_lt _ hg) x]
  change |(((∑ s ∈ Finset.range h, sourcePrefixCount h g j s (b s)) +
    (if r < j then 1 else 0) : ℕ) : ℤ) - ((∑ s ∈ Finset.range h,
    sourcePrefixCount h g r s (b s) : ℕ) : ℤ)| = _
  rw [sum_source_arc_endpoint_identity h g j l hg hj b]
  exact congrArg (fun z : ℕ => |(z:ℤ)-((h*l/g:ℕ):ℤ)|) erase.symm

end Shellsort
end
