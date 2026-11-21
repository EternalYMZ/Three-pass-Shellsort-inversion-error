import Shellsort.ModularDriftLower

/-! Deterministic coefficient geometry and integration of a lower bound
under the actual original-slot Bernoulli mixture. -/
noncomputable section
namespace Shellsort
open scoped BigOperators
open MeasureTheory

theorem onePass_coefficient_norm_lower {n h : ℕ} (hh : 2 ≤ h) (hlen : 2*h ≤ n)
    (i : Fin n) :
    Real.sqrt ((n:ℝ)*h)/4 ≤ Real.sqrt (∑ j : Fin n, firstPassCoefficient h i j ^ 2) := by
  have hp : 0 < h := by omega
  have hL : 2 ≤ tagChainLength h i := by
    have hq : 2 ≤ n/h := (Nat.le_div_iff_mul_le hp).mpr hlen
    change 2 ≤ (chainPositions n h (i.val%h)).card
    rw [actual_chain_length n h hp ⟨i.val%h, Nat.mod_lt _ hp⟩]
    unfold sourceTrialLength
    split <;> omega
  have rlt : ((i.val % h : ℕ):ℝ) < h := by exact_mod_cast Nat.mod_lt i.val hp
  have hnxt : (n:ℝ) ≤ ((i.val%h : ℕ):ℝ) + (h:ℝ)*tagChainLength h i := by
    exact_mod_cast tagChainLength_next h hp i
  have hL2 : (2:ℝ) ≤ tagChainLength h i := by exact_mod_cast hL
  have h2 : (2:ℝ) ≤ h := by exact_mod_cast hh
  have hLn : (tagChainLength h i : ℝ) ≤ n := by exact_mod_cast tagChainLength_le h i
  have hnL : (n:ℝ) ≤ 3*h*((tagChainLength h i:ℝ)-1) := by
    nlinarith [mul_nonneg (show 0 ≤ (h:ℝ) by positivity) (sub_nonneg.mpr hL2)]
  have hsq : (h:ℝ)^2 ≤ 4*((h:ℝ)-1)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h2) (show 0 ≤ 3*(h:ℝ)-2 by linarith)]
  have bound : (n:ℝ)*h ≤ 16*(∑ j : Fin n, firstPassCoefficient h i j ^ 2) := by
    rw [firstPassCoefficient_sq_sum]
    nlinarith [mul_le_mul_of_nonneg_right hnL (Nat.cast_nonneg h),
      mul_le_mul_of_nonneg_right hsq (show 0 ≤ (tagChainLength h i:ℝ)-1 by linarith),
      mul_nonneg (show 0 ≤ (tagChainLength h i:ℝ)-1 by linarith) (sq_nonneg ((h:ℝ)-1))]
  have hroot := Real.sqrt_le_sqrt bound
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 16), show Real.sqrt 16 = 4 by norm_num] at hroot
  linarith

/-- A bound on the central half of the true tagged Bernoulli mixture
survives with factor 1/2 when the original input is a uniform permutation. -/
theorem uniform_onePass_tag_abs_lower_of_central {n h : ℕ} (hh : 0 < h) (i : Fin n)
    (B : ℝ)
    (central : ∀ t : ℝ, 1/4 ≤ t → t ≤ 3/4 →
      B ≤ mean (bernoulliVectorWeight t n) (fun z => |firstPassBitDisplacement h i z|)) :
    B/2 ≤ uniformAverage (fun p : RankPlacement n =>
      |((gapSort p h (p.symm i)).val : ℝ) - ((p.symm i).val : ℝ)|) := by
  let f : TaggedSubset i → ℝ := fun b => |firstPassSubsetDisplacement h i b.val|
  let F := fun z : Fin n → Bool => |firstPassBitDisplacement h i z|
  let A := fun t : ℝ => mean (bernoulliVectorWeight t n) F
  have hcont : Continuous A := bernoulli_product_mean_continuous F
  simp_rw [actual_onePass_tag_displacement _ h hh i]
  change B/2 ≤ uniformAverage (fun p : RankPlacement n => f (tagLowerState p i))
  rw [uniform_tagged_bernoulli_mixture]
  have full (t : ℝ) :
      A t = mean (productWeight (fun _j : {j : Fin n // j ≠ i} => bernoulliWeight t))
        (fun x => f ((omittedBitsSubsetEquiv i) x)) := by
    rw [← bernoulli_mean_add_dummy]
    unfold A F f
    simp_rw [← fullBits_onePass_displacement]
    rfl
  simp_rw [← full]
  have pos : 0 ≤ᵐ[volume.restrict (Set.Ioc (0:ℝ) 1)] A := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with t ht
    exact Finset.sum_nonneg fun z _ => mul_nonneg
      (bernoulliVectorWeight_nonneg t ⟨ht.1.le,ht.2⟩ n z) (abs_nonneg _)
  calc
    B/2 = ∫ _t : ℝ in (1/4)..(3/4), B := by simp; ring
    _ ≤ ∫ t : ℝ in (1/4)..(3/4), A t := by
      exact intervalIntegral.integral_mono_on (by norm_num) (continuous_const.intervalIntegrable _ _)
        (hcont.intervalIntegrable _ _) (fun t ht => central t ht.1 ht.2)
    _ ≤ _ := intervalIntegral.integral_mono_interval (by norm_num) (by norm_num)
      (by norm_num) pos (hcont.intervalIntegrable _ _)

end Shellsort
end
