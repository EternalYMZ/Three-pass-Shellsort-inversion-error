import Shellsort.AllGapThreePassLower
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! A lower bound from the deterministic mean drift of an original-slot
tag, integrated against its true uniform-permutation source model. -/
noncomputable section
namespace Shellsort
open scoped BigOperators
open MeasureTheory

private theorem drift_test_integral (r a : ℝ) :
    (∫ t : ℝ in 0..1, (1-3*t/2) * (r+t*a)) = r/4 := by
  have poly (t : ℝ) : (1-3*t/2) * (r+t*a) = r+(a-3*r/2)*t+(-3*a/2)*t^2 := by ring
  simp_rw [poly]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_id, integral_pow]
  · simp
    <;> ring
  all_goals apply Continuous.intervalIntegrable; fun_prop

/-- The multiplier kills the slope of the conditional mean for every
chain length, leaving one quarter of the original residue. -/
theorem uniform_onePass_tag_abs_drift_lower {n : ℕ} (d : ℕ) (hd : 0 < d) (i : Fin n) :
    ((i.val % d : ℕ) : ℝ)/4 ≤ uniformAverage (fun p : RankPlacement n =>
      |((gapSort p d (p.symm i)).val : ℝ) - ((p.symm i).val : ℝ)|) := by
  let r : ℝ := (i.val % d : ℕ)
  let a := ∑ j : Fin n, firstPassCoefficient d i j
  let f : TaggedSubset i → ℝ := fun B => |firstPassSubsetDisplacement d i B.val|
  let F := fun z : Fin n → Bool => |firstPassBitDisplacement d i z|
  simp_rw [actual_onePass_tag_displacement _ d hd i]
  change r/4 ≤ uniformAverage (fun p : RankPlacement n => f (tagLowerState p i))
  rw [uniform_tagged_bernoulli_mixture, ← drift_test_integral r a]
  have full (t : ℝ) :
      mean (bernoulliVectorWeight t n) F =
      mean (productWeight (fun _j : {j : Fin n // j ≠ i} => bernoulliWeight t))
        (fun x => f ((omittedBitsSubsetEquiv i) x)) := by
    rw [← bernoulli_mean_add_dummy]
    unfold F f
    simp_rw [← fullBits_onePass_displacement]
    rfl
  simp_rw [← full]
  apply intervalIntegral.integral_mono_on zero_le_one
  · apply Continuous.intervalIntegrable; fun_prop
  · exact (bernoulli_product_mean_continuous F).intervalIntegrable 0 1
  intro t ht
  change (1-3*t/2)*(r+t*a) ≤ mean (bernoulliVectorWeight t n) F
  rw [show r+t*a = mean (bernoulliVectorWeight t n) (firstPassBitDisplacement d i)
    from (firstPassBitDisplacement_mean d i t).symm]
  unfold mean
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  have hz := bernoulliVectorWeight_nonneg t ht n z
  have factor : |1-3*t/2| ≤ 1 := abs_le.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
  let x := firstPassBitDisplacement d i z
  have bound : (1-3*t/2)*x ≤ |x| := calc
    _ ≤ |(1-3*t/2)*x| := le_abs_self _
    _ = |1-3*t/2| * |x| := abs_mul _ _
    _ ≤ 1 * |x| := mul_le_mul_of_nonneg_right factor (abs_nonneg x)
    _ = _ := one_mul _
  change _ ≤ bernoulliVectorWeight t n z * |x|
  nlinarith [mul_le_mul_of_nonneg_left bound hz]

private theorem sum_residues_lower (n d : ℕ) (hd : 0 < d) (hdn : d ≤ n) :
    (n:ℝ)*((d:ℝ)-1)/4 ≤ ∑ i : Fin n, ((i.val % d : ℕ) : ℝ) := by
  have hq : 1 ≤ n/d := Nat.div_pos hdn hd
  have rem := Nat.mod_lt n hd
  have eqn := Nat.mod_add_div n d
  have cover : n ≤ 2*(d*(n/d)) := by
    have one := Nat.mul_le_mul_left d hq
    omega
  have coverR : (n:ℝ) ≤ 2*((d:ℝ)*((n/d : ℕ):ℝ)) := by exact_mod_cast cover
  have dr : (1:ℝ) ≤ d := by exact_mod_cast hd
  calc
    _ ≤ ((n/d : ℕ):ℝ) * ((d:ℝ)*((d:ℝ)-1)/2) := by
      nlinarith [mul_le_mul_of_nonneg_right coverR (sub_nonneg.mpr dr)]
    _ = ∑ s : Fin d, ((n/d : ℕ):ℝ)*(s.val:ℝ) := by
      rw [← Finset.mul_sum, sum_fin_values_real]
    _ ≤ _ := by
      rw [← (positionChainEquiv n d hd).symm.sum_comp, Fintype.sum_sigma]
      apply Finset.sum_le_sum
      intro s _
      simp only [positionChainEquiv_symm_residue, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg s.val)
      exact_mod_cast (show n/d ≤ sourceTrialLength (n/d) (n%d) s.val by
        unfold sourceTrialLength; split <;> omega)

/-- Uniform in all array lengths and active positive gaps. -/
theorem uniform_onePass_footrule_drift_lower (n d : ℕ) (hd : 0 < d) (hdn : d ≤ n) :
    (n:ℝ)*((d:ℝ)-1)/16 ≤ uniformAverage (fun p : RankPlacement n => footrule (gapSort p d)) := by
  rw [uniform_onePass_footrule_by_original_positions]
  have first := sum_residues_lower n d hd hdn
  apply le_trans _ (Finset.sum_le_sum fun (i : Fin n) _ => uniform_onePass_tag_abs_drift_lower d hd i)
  rw [← Finset.sum_div]
  linarith

/-- Unconditional large-divisor region, for both executed counters. -/
theorem uniform_threePass_lower_of_large_common_divisor (n h g d : ℕ) (hh : 0<h) (hg : 0<g)
    (hd : 2 ≤ d) (hdn : d ≤ n) (hn : n ≤ d^2) (hdh : d ∣ h) (hdg : d ∣ g) :
    (n:ℝ)*Real.sqrt n/64 ≤ uniformAverage
      (fun p : RankPlacement n => (threePassInsertionCost p h g hh hg : ℝ)) ∧
    (n:ℝ)*Real.sqrt n/64 ≤ uniformAverage
      (fun p : RankPlacement n => (threePassComparisonCost p h g hh hg : ℝ)) := by
  have residual := (uniform_onePass_footrule_drift_lower n d (by omega) hdn).trans
    ((uniform_common_gap_footrule_le_twoPass n h g d hdh hdg).trans
      (uniform_threePass_checkpoint_transport n h g hh hg).2)
  have ds : (n:ℝ) ≤ (d:ℝ)^2 := by exact_mod_cast hn
  have d2 : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hsq := Real.sq_sqrt (Nat.cast_nonneg n)
  have hr : Real.sqrt (n:ℝ) ≤ (d:ℝ) := by nlinarith [Real.sqrt_nonneg (n:ℝ)]
  have bound := mul_le_mul_of_nonneg_left (show Real.sqrt (n:ℝ) ≤ 2*((d:ℝ)-1) by linarith)
    (Nat.cast_nonneg n)
  have shifts : (n:ℝ)*Real.sqrt n/64 ≤ uniformAverage
      (fun p : RankPlacement n => (threePassInsertionCost p h g hh hg : ℝ)) := by linarith
  exact ⟨shifts, shifts.trans (uniform_threePassComparisonCost_bounds n h g hh hg).1⟩

/-- Large separation between the two gaps forces shifts even when the
gaps are coprime. The argument uses only the first checkpoint. -/
theorem uniform_threePass_lower_of_gap_separation (n h g : ℕ)
    (hh : 2 ≤ h) (hg : 0 < g) (hhN : h ≤ n)
    (separation : (g:ℝ)*Real.sqrt n ≤ (h:ℝ)) :
    (n:ℝ)*Real.sqrt n/64 ≤ uniformAverage
      (fun p : RankPlacement n => (threePassInsertionCost p h g (by omega) hg : ℝ)) ∧
    (n:ℝ)*Real.sqrt n/64 ≤ uniformAverage
      (fun p : RankPlacement n => (threePassComparisonCost p h g (by omega) hg : ℝ)) := by
  have hpos : 0 < h := by omega
  have residual := (uniform_onePass_footrule_drift_lower n h hpos hhN).trans
    (uniform_threePass_checkpoint_transport n h g hpos hg).1
  have hr : (2:ℝ) ≤ h := by exact_mod_cast hh
  have bound := mul_le_mul_of_nonneg_left
    (show (g:ℝ)*Real.sqrt n ≤ 2*((h:ℝ)-1) by linarith)
    (Nat.cast_nonneg n)
  have shifts : (n:ℝ)*Real.sqrt n/64 ≤ uniformAverage
      (fun p : RankPlacement n => (threePassInsertionCost p h g hpos hg : ℝ)) := by
    apply le_of_mul_le_mul_left (a := 2*(g:ℝ)) _ (by positivity)
    nlinarith only [residual, bound]
  exact ⟨shifts, shifts.trans (uniform_threePassComparisonCost_bounds n h g hpos hg).1⟩

end Shellsort
end
