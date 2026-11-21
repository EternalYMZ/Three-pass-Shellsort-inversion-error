import Shellsort.PoissonBinomialDeviation
import Shellsort.TaggedUpper
import Shellsort.OnePassLowerGeometry

/-! The genuine lower-key subset of a fixed original key determines a count of
source endpoints on the selected cyclic arc. This module transports a per-owner
variance bound for that count to the uniform permutation law. -/
noncomputable section
namespace Shellsort
open scoped BigOperators
open MeasureTheory

/-- Arc starting just after the owner endpoint and ending after ell increments. -/
def pivotArcSites (h g owner ell y : ℕ) : Finset ℕ :=
  (Finset.range ell).image (fun d => (owner+h*y+h*(d+1))%g)

/-- The hit test evaluated at one source's count. The owner is always omitted. -/
def pivotArcHit (h g owner ell y s count : ℕ) : Bool :=
  decide (s ≠ owner ∧ (s+h*count)%g ∈ pivotArcSites h g owner ell y)

/-- Arc count read directly from a set of original slots with smaller keys. -/
def taggedSubsetArcCount {n : ℕ} (h g ell : ℕ) (i : Fin n) (B : Finset (Fin n)) : ℕ :=
  bitCount (fun s : Fin h => pivotArcHit h g (i.val%h) ell
    (chainLowerCount B h (i.val%h)) s.val (chainLowerCount B h s.val))

private def sourceArcEvent (h g m rem ell : ℕ) (owner : Fin h) (y : ℕ)
    (s : Fin h) (bits : Fin (sourceTrialLength m rem s.val) → Bool) : Bool :=
  pivotArcHit h g owner.val ell y s.val (bitCount bits)

/-- Sum of the hit variances for all sources of their actual sizes, at a
specified owner count and threshold t. The owner summand is zero. -/
def sourceArcVariance (h g m rem ell : ℕ) (owner : Fin h) (t : ℝ) (y : ℕ) : ℝ :=
  let p := fun s => eventMarginal (sourceCoordinateWeight h m rem t s)
    (sourceArcEvent h g m rem ell owner y s)
  ∑ s, p s*(1-p s)

private lemma fullBits_arcCount {n h : ℕ} (hh : 0 < h) (g ell : ℕ) (i : Fin n)
    (z : Fin n → Bool) :
    let coord := positionChainEquiv n h hh i
    let y := ownerBitCount coord.2 (chainBits hh z coord.1)
    taggedSubsetArcCount h g ell i (fullBitsSubset i z) =
      bitCount (fun s => sourceArcEvent h g (n/h) (n%h) ell coord.1 y s (chainBits hh z s)) := by
  let owner := ((positionChainEquiv n h hh) i).1
  have residue : owner.val = i.val%h := rfl
  dsimp only
  unfold taggedSubsetArcCount
  rw [← residue,owner_fullBits_chain_count hh i z]
  apply congrArg bitCount
  funext s
  by_cases hs : s = owner
  · subst s; simp [sourceArcEvent,pivotArcHit,owner]
  · have hne : s.val ≠ i.val%h := fun eq => hs (Fin.ext (eq.trans residue.symm))
    rw [nonowner_fullBits_chain_count hh i z s hne]
    rfl

/-- Under independent threshold bits, the genuine selected arc has the
conditional variance lower bound averaged over true owner bits. -/
theorem fullBits_pivotArc_abs_lower {n h : ℕ} (hh : 0 < h) (g ell : ℕ)
    (i : Fin n) (t K : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) :
    let coord := positionChainEquiv n h hh i
    let v := fun a => sourceArcVariance h g (n/h) (n%h) ell coord.1 t (ownerBitCount coord.2 a)
    mean (sourceCoordinateWeight h (n/h) (n%h) t coord.1)
        (fun a => v a/Real.sqrt (1+6*v a)) ≤
      mean (bernoulliVectorWeight t n)
        (fun z => |(taggedSubsetArcCount h g ell i (fullBitsSubset i z) : ℝ)-K|) := by
  let coord := positionChainEquiv n h hh i
  let w := sourceCoordinateWeight h (n/h) (n%h) t
  let event := fun a => sourceArcEvent h g (n/h) (n%h) ell coord.1 (ownerBitCount coord.2 a)
  have ignore : ∀ a y, event a coord.1 y = false := by
    intros; simp [event,sourceArcEvent,pivotArcHit]
  have raw := owner_selected_event_abs_lower w coord.1 event ignore
    (sourceCoordinateWeight_nonneg h (n/h) (n%h) t ht) (sourceCoordinateWeight_sum h (n/h) (n%h) t)
    (fun _ => K)
  simp_rw [fullBits_arcCount hh g ell i]
  unfold bernoulliVectorWeight
  rw [fullBits_mean_chainBits n h hh t (fun x => |(bitCount (fun s =>
    event (x coord.1) s (x s)) : ℝ)-K|)]
  exact raw

/-- For actual uniform input permutations, it suffices to verify explicitly
computed variances on the central thresholds and attainable owner counts. -/
theorem uniform_pivotArc_abs_lower_of_central_variance {n h : ℕ} (hh : 0 < h)
    (g ell : ℕ) (i : Fin n) (K A : ℝ) (hA : 1 ≤ A)
    (variance : ∀ t : ℝ, 1/4 ≤ t → t ≤ 3/4 →
      let coord := positionChainEquiv n h hh i
      ∀ a, A/768 ≤ sourceArcVariance h g (n/h) (n%h) ell coord.1 t (ownerBitCount coord.2 a)) :
    Real.sqrt A / 1600 ≤ uniformAverage (fun p : RankPlacement n =>
      |(taggedSubsetArcCount h g ell i (tagLowerState p i).val : ℝ)-K|) := by
  let coord := positionChainEquiv n h hh i
  let f (b : TaggedSubset i) := |(taggedSubsetArcCount h g ell i b.val : ℝ)-K|
  let F (z : Fin n → Bool) := |(taggedSubsetArcCount h g ell i (fullBitsSubset i z) : ℝ)-K|
  let R (t : ℝ) := mean (bernoulliVectorWeight t n) F
  have central (t : ℝ) (htl : 1/4 ≤ t) (htu : t ≤ 3/4) : Real.sqrt A/800 ≤ R t := by
    have ht : 0 ≤ t ∧ t ≤ 1 := ⟨by linarith,by linarith⟩
    apply le_trans _ (fullBits_pivotArc_abs_lower hh g ell i t K ht)
    let w := sourceCoordinateWeight h (n/h) (n%h) t coord.1
    rw [← mean_const w (sourceCoordinateWeight_sum h (n/h) (n%h) t coord.1) (Real.sqrt A/800)]
    apply Finset.sum_le_sum
    intro a _
    exact mul_le_mul_of_nonneg_left (perArc_absolute_lower_of_variance hA (variance t htl htu a))
      (sourceCoordinateWeight_nonneg h (n/h) (n%h) t ht coord.1 a)
  have hcont : Continuous R := bernoulli_product_mean_continuous F
  change _ ≤ uniformAverage (fun p : RankPlacement n => f (tagLowerState p i))
  rw [uniform_tagged_bernoulli_mixture]
  have full (t : ℝ) : R t = mean
      (productWeight (fun _j : {j : Fin n // j ≠ i} => bernoulliWeight t))
      (fun x => f ((omittedBitsSubsetEquiv i) x)) := by
    rw [← bernoulli_mean_add_dummy]
    rfl
  simp_rw [← full]
  have pos : 0 ≤ᵐ[volume.restrict (Set.Ioc (0:ℝ) 1)] R := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with t ht
    exact Finset.sum_nonneg fun z _ => mul_nonneg
      (bernoulliVectorWeight_nonneg t ⟨ht.1.le,ht.2⟩ n z) (abs_nonneg _)
  calc
    Real.sqrt A / 1600 = ∫ _t : ℝ in (1/4)..(3/4), Real.sqrt A/800 := by simp; ring
    _ ≤ ∫ t : ℝ in (1/4)..(3/4), R t :=
      intervalIntegral.integral_mono_on (by norm_num) (continuous_const.intervalIntegrable _ _)
        (hcont.intervalIntegrable _ _) (fun t ht => central t ht.1 ht.2)
    _ ≤ _ := intervalIntegral.integral_mono_interval (by norm_num) (by norm_num)
      (by norm_num) pos (hcont.intervalIntegrable _ _)

end Shellsort
end

