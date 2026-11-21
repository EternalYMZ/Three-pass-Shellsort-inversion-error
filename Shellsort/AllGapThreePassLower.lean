import Shellsort.NaturalComparisonBounds
import Shellsort.WordShiftDistance
import Shellsort.ModularCut

/-! Lower bounds for the ordinary three-pass counters from the actual two
checkpoint states. The final theorem takes the unresolved distributional
lower estimates as explicit hypotheses in precisely the branches that use
them. Only the small-first-gap branch is unconditional here. -/
noncomputable section
namespace Shellsort

/-- The remaining two passes must transport the first checkpoint to the
identity; the last pass must transport the second checkpoint on its own. -/
theorem threePass_checkpoint_transport {n : ℕ} (p : RankPlacement n) (h g : ℕ)
    (hh : 0 < h) (hg : 0 < g) :
    footrule (gapSort p h) ≤ 2 * (g : ℝ) * (threePassInsertionCost p h g hh hg : ℝ) ∧
    footrule (gapSort (gapSort p h) g) ≤ 2 * (threePassInsertionCost p h g hh hg : ℝ) := by
  let a := gapSort p h
  let b := gapSort a g
  have hz : footrule (Equiv.refl (Fin n)) = 0 := by simp [footrule, transport]
  have s := footrule_le_wordShiftDistance a [⟨g,hg⟩, ⟨1,by decide⟩]
  have t := footrule_le_wordShiftDistance b [⟨1,by decide⟩]
  simp only [List.map_cons, List.map_nil, sortWord, wordShiftDistance, gapSort_one, hz,
    Nat.cast_one, one_mul, add_zero, zero_add] at s t
  have gp : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have pay := mul_le_mul_of_nonneg_right gp (Nat.cast_nonneg (gapInsertionCost b 1 (by decide)) : (0:ℝ) ≤ _)
  have hp : (0:ℝ) ≤ (gapInsertionCost p h hh : ℝ) := Nat.cast_nonneg _
  have ha : (0:ℝ) ≤ (gapInsertionCost a g hg : ℝ) := Nat.cast_nonneg _
  change footrule a ≤ _ ∧ footrule b ≤ _
  simp only [threePassInsertionCost, Nat.cast_add]
  change footrule a ≤ 2*(g:ℝ)*((gapInsertionCost p h hh : ℝ) +
      (gapInsertionCost a g hg : ℝ) + (gapInsertionCost b 1 (by decide) : ℝ)) ∧
    footrule b ≤ 2*((gapInsertionCost p h hh : ℝ) +
      (gapInsertionCost a g hg : ℝ) + (gapInsertionCost b 1 (by decide) : ℝ))
  change footrule a ≤ 2*((g:ℝ)*(gapInsertionCost a g hg : ℝ) +
      (gapInsertionCost b 1 (by decide) : ℝ)) at s
  constructor
  · nlinarith [mul_nonneg (Nat.cast_nonneg g : (0:ℝ) ≤ g) hp]
  · linarith

/-- The averages use the same initially uniform permutation throughout. -/
theorem uniform_threePass_checkpoint_transport (n h g : ℕ) (hh : 0 < h) (hg : 0 < g) :
    uniformAverage (fun p : RankPlacement n => footrule (gapSort p h)) ≤
      (2 * (g : ℝ)) * uniformAverage (fun p : RankPlacement n => (threePassInsertionCost p h g hh hg : ℝ)) ∧
    uniformAverage (fun p : RankPlacement n => footrule (gapSort (gapSort p h) g)) ≤
      2 * uniformAverage (fun p : RankPlacement n => (threePassInsertionCost p h g hh hg : ℝ)) := by
  constructor
  · rw [← uniformAverage_const_mul]
    exact uniformAverage_mono _ _ fun p => (threePass_checkpoint_transport p h g hh hg).1
  · rw [← uniformAverage_const_mul]
    exact uniformAverage_mono _ _ fun p => (threePass_checkpoint_transport p h g hh hg).2

/-- Any common divisor gives an unconditional one-pass lower bound for
the actual two-pass residual. This allows the noncoprime branch to use
only a distributional estimate for one ordinary gap. -/
theorem uniform_common_gap_footrule_le_twoPass (n h g d : ℕ)
    (hdh : d ∣ h) (hdg : d ∣ g) :
    uniformAverage (fun p : RankPlacement n => footrule (gapSort p d)) ≤
    uniformAverage (fun p : RankPlacement n => footrule (gapSort (gapSort p h) g)) := by
  apply uniformAverage_mono
  intro p
  exact divisible_word_footrule_lower p [h,g] (by simpa using And.intro hdh hdg)

/-- Unconditional for all second gaps: the first executed pass suffices. -/
theorem uniform_threePass_lower_of_first_gap_sq_le (n h g : ℕ) (hn : 4 ≤ n)
    (hh : 0 < h) (hg : 0 < g) (hs : h^2 ≤ n) :
    (n:ℝ) * Real.sqrt n / 8 ≤
      uniformAverage (fun p : RankPlacement n => (threePassInsertionCost p h g hh hg : ℝ)) := by
  apply le_trans _ (uniform_threePassInsertionCost_lower n h g hh hg)
  have hp : (0 : ℝ) < h := by exact_mod_cast hh
  have sq : (h:ℝ)^2 ≤ n := by exact_mod_cast hs
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have root := Real.sq_sqrt (Nat.cast_nonneg n)
  have rpos := Real.sqrt_nonneg (n:ℝ)
  have hr : (h:ℝ) ≤ Real.sqrt n := by nlinarith
  have rr : (2:ℝ) ≤ Real.sqrt n := by nlinarith
  have budget : (h:ℝ) * (Real.sqrt n + 2) ≤ 2 * n := by
    have a := mul_le_mul_of_nonneg_right hr (show 0 ≤ Real.sqrt n + 2 by linarith)
    nlinarith [mul_nonneg rpos (sub_nonneg.mpr rr)]
  rw [le_sub_iff_add_le, le_div_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left budget (Nat.cast_nonneg n : (0:ℝ) ≤ n)]

/-- Both coprime fluctuation scales dominate the target on the large-gap
branch. This step is purely numerical and includes regime equality. -/
theorem lower_twoPass_scales_of_large_gaps {n h g : ℝ} (hn : 0 ≤ n) (hh : 0 ≤ h)
    (hg : 0 ≤ g) (hsmall : n ≤ h^2) (gsmall : h ≤ g^2) :
    Real.sqrt n ≤ min (g * Real.sqrt h) (Real.sqrt g * Real.sqrt (Real.sqrt (n*h))) := by
  have hsq := Real.sq_sqrt hh
  have nsq := Real.sq_sqrt hn
  have gsq := Real.sq_sqrt hg
  have hp := Real.sqrt_nonneg h
  have np := Real.sqrt_nonneg n
  have gp := Real.sqrt_nonneg g
  have g_ge : Real.sqrt h ≤ g := by nlinarith
  have h_ge : Real.sqrt n ≤ h := by nlinarith
  have w : Real.sqrt n ≤ g * Real.sqrt h := by
    nlinarith [mul_le_mul_of_nonneg_right g_ge hp]
  refine le_min w ?_
  have gp' := Real.sqrt_nonneg (Real.sqrt (n*h))
  have square : (Real.sqrt g * Real.sqrt (Real.sqrt (n*h))) ^ 2 =
      g * (Real.sqrt n * Real.sqrt h) := by
    rw [mul_pow, gsq, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sqrt_mul hn]
  have ge := mul_le_mul_of_nonneg_left w np
  nlinarith [mul_nonneg gp gp']

/-- If the stated true-checkpoint lower estimates hold with one common
constant, the same constant works for the executed right shifts and key
comparisons. The first-gap estimate is needed only after the exact
first-pass mean has ceased to suffice. -/
theorem uniform_threePass_lower_of_checkpoint_estimates (n h g : ℕ)
    (hn : 4 ≤ n) (hh : 0 < h) (hg : 0 < g)
    (c : ℝ) (hc : 0 ≤ c) (hc8 : c ≤ 1/8)
    (first : n < h^2 → g^2 ≤ h →
      2*c*(n:ℝ)*Real.sqrt ((n:ℝ)*h) ≤
        uniformAverage (fun p : RankPlacement n => footrule (gapSort p h)))
    (coprime : n < h^2 → h < g^2 → Nat.Coprime h g →
      2*c*(n:ℝ)*min ((g:ℝ)*Real.sqrt h)
        (Real.sqrt g * Real.sqrt (Real.sqrt ((n:ℝ)*h))) ≤
        uniformAverage (fun p : RankPlacement n => footrule (gapSort (gapSort p h) g)))
    (common : n < h^2 → h < g^2 → ¬Nat.Coprime h g →
      2*c*(n:ℝ)*Real.sqrt n ≤
        uniformAverage (fun p : RankPlacement n => footrule (gapSort p (h.gcd g)))) :
    c*(n:ℝ)*Real.sqrt n ≤
        uniformAverage (fun p : RankPlacement n => (threePassInsertionCost p h g hh hg : ℝ)) ∧
    c*(n:ℝ)*Real.sqrt n ≤
        uniformAverage (fun p : RankPlacement n => (threePassComparisonCost p h g hh hg : ℝ)) := by
  suffices shifts : c*(n:ℝ)*Real.sqrt n ≤
      uniformAverage (fun p : RankPlacement n => (threePassInsertionCost p h g hh hg : ℝ)) from
    ⟨shifts, shifts.trans (uniform_threePassComparisonCost_bounds n h g hh hg).1⟩
  by_cases small : h^2 ≤ n
  · apply le_trans _ (uniform_threePass_lower_of_first_gap_sq_le n h g hn hh hg small)
    nlinarith [mul_le_mul_of_nonneg_right hc8
      (mul_nonneg (Nat.cast_nonneg n) (Real.sqrt_nonneg (n:ℝ)))]
  have large := lt_of_not_ge small
  obtain ⟨t₁,t₂⟩ := uniform_threePass_checkpoint_transport n h g hh hg
  by_cases short : g^2 ≤ h
  · have geom := (first large short).trans t₁
    rw [Real.sqrt_mul (Nat.cast_nonneg n)] at geom
    have gsq : (g:ℝ)^2 ≤ h := by exact_mod_cast short
    have gp : (0:ℝ) < g := by exact_mod_cast hg
    have gr : (g:ℝ) ≤ Real.sqrt h := by
      have := Real.sq_sqrt (Nat.cast_nonneg h)
      have := Real.sqrt_nonneg (h:ℝ)
      nlinarith
    have coeff : 0 ≤ 2*c*(n:ℝ)*Real.sqrt n := by positivity
    have scaled := mul_le_mul_of_nonneg_left gr coeff
    apply le_of_mul_le_mul_left (a := 2*(g:ℝ)) _ (by positivity)
    calc
      _ = (2*c*(n:ℝ)*Real.sqrt n)*g := by ring
      _ ≤ _ := scaled
      _ = 2*c*(n:ℝ)*(Real.sqrt n*Real.sqrt h) := by ring
      _ ≤ _ := geom
  · have long := lt_of_not_ge short
    by_cases cop : Nat.Coprime h g
    · have geom := (coprime large long cop).trans t₂
      have hn' : (n:ℝ) ≤ (h:ℝ)^2 := by exact_mod_cast large.le
      have hg' : (h:ℝ) ≤ (g:ℝ)^2 := by exact_mod_cast long.le
      have w := lower_twoPass_scales_of_large_gaps (Nat.cast_nonneg n) (Nat.cast_nonneg h)
        (Nat.cast_nonneg g) hn' hg'
      have bound := mul_le_mul_of_nonneg_left w (show 0 ≤ 2*c*(n:ℝ) by positivity)
      linarith
    · have canon := uniform_common_gap_footrule_le_twoPass n h g (h.gcd g)
          (Nat.gcd_dvd_left h g) (Nat.gcd_dvd_right h g)
      linarith only [((common large long cop).trans canon).trans t₂]

end Shellsort
end
