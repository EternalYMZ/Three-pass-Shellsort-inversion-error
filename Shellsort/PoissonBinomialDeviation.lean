import Shellsort.ProductTransport

/-! Absolute deviation about arbitrary centers for independent event counts. -/
noncomputable section
namespace Shellsort
open scoped BigOperators

private def bitLaw {n : ℕ} (p : Fin n → ℝ) :=
  productWeight (fun i => bernoulliWeight (p i))

private def centeredCount {n : ℕ} (p : Fin n → ℝ) (z : Fin n → Bool) : ℝ :=
  ∑ i, ((if z i then (1 : ℝ) else 0) - p i)

private def varianceSum {n : ℕ} (p : Fin n → ℝ) : ℝ := ∑ i, p i * (1 - p i)

private lemma mean_scale_count {α : Type*} [Fintype α] (w f : α → ℝ) (a : ℝ) :
    mean w (fun x => a * f x) = a * mean w f := by
  simp only [mean, Finset.mul_sum, mul_left_comm]

private lemma mean_mono_count {α : Type*} [Fintype α] (w : α → ℝ) (hw : ∀ x, 0 ≤ w x)
    {f g : α → ℝ} (h : ∀ x, f x ≤ g x) : mean w f ≤ mean w g :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (hw x)

private lemma bitLaw_total {n : ℕ} (p : Fin n → ℝ) : ∑ z, bitLaw p z = 1 :=
  productWeight_sum _ fun i => bernoulliWeight_sum (p i)

private lemma splitCount {n : ℕ} (p : Fin (n+1) → ℝ) (f : ℝ → ℝ) :
    mean (bitLaw p) (fun z => f (centeredCount p z)) =
      mean (bitLaw (fun i : Fin n => p i.succ)) (fun z =>
        p 0 * f ((1 - p 0) + centeredCount (fun i : Fin n => p i.succ) z) +
        (1-p 0) * f ((0 - p 0) + centeredCount (fun i : Fin n => p i.succ) z)) := by
  unfold mean
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.consEquiv_apply, bitLaw, productWeight,
    Fin.prod_univ_succ, centeredCount, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Fintype.sum_bool, bernoulliWeight, ite_true, Bool.false_eq_true, ite_false,
    mul_add, Finset.sum_add_distrib]
  apply congrArg₂ (· + ·) <;> apply Finset.sum_congr rfl <;> intros <;> ring

private theorem centered_count_moments {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    mean (bitLaw p) (centeredCount p) = 0 ∧
    mean (bitLaw p) (fun z => (centeredCount p z)^2) = varianceSum p ∧
    mean (bitLaw p) (fun z => (centeredCount p z)^4) ≤ varianceSum p + 3*(varianceSum p)^2 := by
  induction n with
  | zero => simp [centeredCount, varianceSum, mean]
  | succ n ih =>
    let tail (i : Fin n) := p i.succ
    let w := bitLaw tail
    let s := centeredCount tail
    let A := varianceSum tail
    let b := p 0
    let v := b*(1-b)
    have ⟨h1,h2,h4⟩ := ih tail (fun i => hp i.succ)
    change mean w s = 0 at h1
    change mean w (fun z => (s z)^2) = A at h2
    change mean w (fun z => (s z)^4) ≤ A+3*A^2 at h4
    have hw : ∑ z, w z = 1 := bitLaw_total tail
    have total : varianceSum p = v+A := Fin.sum_univ_succ _
    have B1 (x : ℝ) : b*((1-b)+x)+(1-b)*((0-b)+x)=x := by ring
    have B2 (x : ℝ) : b*((1-b)+x)^2+(1-b)*((0-b)+x)^2=x^2+v := by dsimp [v]; ring
    have B4 (x : ℝ) : b*((1-b)+x)^4+(1-b)*((0-b)+x)^4 =
        ((x^4+(6*v)*x^2)+(4*v*(1-2*b))*x)+v*(1-3*v) := by dsimp [v]; ring
    constructor
    · rw [show mean (bitLaw p) (centeredCount p) = _ from splitCount p id]
      change mean w (fun z => b*((1-b)+s z)+(1-b)*((0-b)+s z)) = 0
      simpa only [B1] using h1
    constructor
    · rw [splitCount p (fun x => x^2), total]
      change mean w (fun z => b*((1-b)+s z)^2+(1-b)*((0-b)+s z)^2) = v+A
      simp only [B2, mean_add, mean_const w hw, h2, add_comm]
    · rw [splitCount p (fun x => x^4), total]
      change mean w (fun z => b*((1-b)+s z)^4+(1-b)*((0-b)+s z)^4) ≤ v+A+3*(v+A)^2
      simp only [B4,mean_add,mean_scale_count,mean_const w hw,h1,h2,mul_zero,add_zero]
      nlinarith [sq_nonneg v]
private lemma abs_from_centered_moments {α : Type*} [Fintype α] (w s : α → ℝ)
    (hw0 : ∀ x, 0 ≤ w x) (hw : ∑ x, w x = 1) (v : ℝ) (hv : 0 ≤ v)
    (h1 : mean w s = 0) (h2 : mean w (fun x => (s x)^2) = v)
    (h4 : mean w (fun x => (s x)^4) ≤ v+3*v^2) (a : ℝ) :
    v/Real.sqrt (1+6*v) ≤ mean w (fun x => |s x-a|) := by
  let m3 := mean w (fun y => (s y)^3)
  let m4 := mean w (fun y => (s y)^4)
  have inner2 (c : ℝ) : mean w (fun y => (c-s y)^2) = c^2+v := by
    have expand (y : α) : (c-s y)^2 = (c^2 - (2*c)*s y) + (s y)^2 := by ring
    simp only [expand,mean_add,mean_sub,mean_scale_count,mean_const w hw,h1,h2,mul_zero,sub_zero]
  have inner4 (c : ℝ) : mean w (fun y => (c-s y)^4) =
      (c^4+(6*v)*c^2)-(4*m3)*c+m4 := by
    have expand (y : α) : (c-s y)^4 =
        (((c^4-(4*c^3)*s y)+(6*c^2)*(s y)^2)-(4*c)*(s y)^3)+(s y)^4 := by ring
    simp only [expand,mean_add,mean_sub,mean_scale_count,mean_const w hw,h1,h2,
      mul_zero,sub_zero,m3,m4]
    ring
  have d2 : mean w (fun x => mean w (fun y => (s x-s y)^2)) = 2*v := by
    simp only [inner2,mean_add,mean_const w hw,h2]; ring
  have d4 : mean w (fun x => mean w (fun y => (s x-s y)^4)) ≤ 2*v+12*v^2 := by
    simp only [inner4,mean_add,mean_sub,mean_scale_count,mean_const w hw,h1,h2,
      mul_zero,sub_zero,m4]
    linarith
  let q := Real.sqrt (1+6*v)
  have hq : 0 < q := Real.sqrt_pos.mpr (by positivity)
  have hq2 : q^2 = 1+6*v := Real.sq_sqrt (by positivity)
  have point (z : ℝ) : 3*q^2*z^2 ≤ 2*q^3*|z|+z^4 := by
    have h := mul_nonneg (mul_nonneg (abs_nonneg z) (show 0 ≤ |z|+2*q by positivity))
      (sq_nonneg (|z|-q))
    have h2z := sq_abs z
    nlinarith only [h, congrArg (fun x : ℝ => x^2) h2z,
      congrArg (fun x : ℝ => q^2*x) h2z]
  have pol := mean_mono_count w hw0 fun x => mean_mono_count w hw0 fun y => point (s x-s y)
  simp only [mean_add,mean_scale_count,d2] at pol
  have triangle := mean_mono_count w hw0 fun x => mean_mono_count w hw0 fun y =>
    (show |s x-s y| ≤ |s x-a|+|s y-a| by
      calc
        _ ≤ |s x-a|+|a-s y| := abs_sub_le (s x) a (s y)
        _ = _ := by rw [abs_sub_comm a])
  simp only [mean_add,mean_const w hw] at triangle
  have twoQ := mul_le_mul_of_nonneg_left triangle (show 0 ≤ 2*q^3 by positivity)
  apply (div_le_iff₀ hq).mpr
  apply le_of_mul_le_mul_left (a := 4*q^2) _ (by positivity)
  nlinarith only [pol, d4, twoQ, congrArg (fun x : ℝ => 2*v*x) hq2]

/-- For fully heterogeneous independent Bernoulli indicators, the expected
absolute deviation of their count about any given real center. -/
theorem poissonBinomial_abs_lower {n : ℕ} (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (K : ℝ) :
    (∑ i, p i*(1-p i)) / Real.sqrt (1+6*∑ i, p i*(1-p i)) ≤
      mean (productWeight (fun i => bernoulliWeight (p i)))
        (fun z => |(bitCount z : ℝ)-K|) := by
  have hw := productWeight_nonneg (fun i => bernoulliWeight (p i))
    (fun i b => bernoulliWeight_nonneg (p i) (hp i) b)
  have hv : 0 ≤ varianceSum p :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hp i).1 (sub_nonneg.mpr (hp i).2)
  obtain ⟨h1,h2,h4⟩ := centered_count_moments p hp
  have lower := abs_from_centered_moments (bitLaw p) (centeredCount p) hw (bitLaw_total p)
    (varianceSum p) hv h1 h2 h4 (K - ∑ i, p i)
  have count_eq (z : Fin n → Bool) :
      centeredCount p z - (K-∑ i, p i) = (bitCount z : ℝ)-K := by
    simp only [centeredCount, Finset.sum_sub_distrib, bitCount,Nat.cast_sum,
      Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    ring
  simpa only [count_eq, varianceSum, bitLaw] using lower

/-- Exact finite event probabilities for the individual sources. -/
def eventMarginal {α : Type*} [Fintype α] (w : α → ℝ) (event : α → Bool) : ℝ :=
  ∑ y, if event y then w y else 0

private lemma event_mass {α : Type*} [Fintype α] (w : α → ℝ) (event : α → Bool)
    (hw : ∑ y, w y = 1) (b : Bool) :
    (∑ y, if event y = b then w y else 0) = bernoulliWeight (eventMarginal w event) b := by
  cases b with
  | true => rfl
  | false =>
    change _ = 1 - (∑ y, if event y then w y else 0)
    apply eq_sub_of_add_eq
    rw [← Finset.sum_add_distrib, ← hw]
    apply Finset.sum_congr rfl
    intro y _
    cases event y <;> simp

/-- Project independent finite sources to their hit indicators. This equality
holds for any observable of the entire indicator vector. -/
theorem productWeight_event_projection {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)] (w : ∀ i, β i → ℝ) (event : ∀ i, β i → Bool)
    (hw : ∀ i, ∑ y, w i y = 1) (f : (ι → Bool) → ℝ) :
    mean (productWeight w) (fun x => f (fun i => event i (x i))) =
      mean (productWeight (fun i => bernoulliWeight (eventMarginal (w i) (event i)))) f := by
  classical
  let fiberWeight (x : ∀ i, β i) (z : ι → Bool) :=
    ∏ i, if event i (x i) = z i then w i (x i) else 0
  have fiber_one (x : ∀ i, β i) (z : ι → Bool) :
      fiberWeight x z = if (fun i => event i (x i)) = z then productWeight w x else 0 := by
    by_cases h : (fun i => event i (x i)) = z
    · subst z
      simp [fiberWeight, productWeight]
    · rw [ite_eq_right h]
      obtain ⟨i,hi⟩ := not_forall.mp (fun h' => h (funext h'))
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  have fibers (z : ι → Bool) :
      (∑ x, fiberWeight x z) =
       productWeight (fun i => bernoulliWeight (eventMarginal (w i) (event i))) z := by
    calc
      _ = ∏ i, ∑ y, if event i y = z i then w i y else 0 :=
        (Fintype.prod_sum (fun i y => if event i y = z i then w i y else 0)).symm
      _ = _ := Finset.prod_congr rfl fun i _ => event_mass (w i) (event i) (hw i) (z i)
  unfold mean
  calc
    _ = ∑ x, ∑ z, fiberWeight x z * f z := by
      apply Finset.sum_congr rfl
      intro x _
      simp [fiber_one, ite_mul]
    _ = ∑ z, (∑ x, fiberWeight x z) * f z := by
      rw [Finset.sum_comm]; simp only [Finset.sum_mul]
    _ = _ := by simp only [fibers]

/-- Direct form for possibly different finite source spaces and an arbitrary
event on each one. There is no nondegeneracy requirement for the marginals. -/
theorem product_event_count_abs_lower {n : ℕ} {β : Fin n → Type*}
    [∀ i, Fintype (β i)] (w : ∀ i, β i → ℝ) (event : ∀ i, β i → Bool)
    (hw0 : ∀ i y, 0 ≤ w i y) (hw : ∀ i, ∑ y, w i y = 1) (K : ℝ) :
    let p := fun i => eventMarginal (w i) (event i)
    let V := ∑ i, p i*(1-p i)
    V/Real.sqrt (1+6*V) ≤ mean (productWeight w)
      (fun x => |(bitCount (fun i => event i (x i)) : ℝ)-K|) := by
  let p := fun i => eventMarginal (w i) (event i)
  have hp (i : Fin n) : 0 ≤ p i ∧ p i ≤ 1 := by
    constructor
    · apply Finset.sum_nonneg
      intro y _
      split <;> simp [hw0]
    · exact (Finset.sum_le_sum (g := w i)
        (fun y _ => by split <;> simp [hw0])).trans (hw i).le
  exact (poissonBinomial_abs_lower p hp K).trans_eq
    (productWeight_event_projection w event hw (fun z => |(bitCount z : ℝ) - K|)).symm

/-- Numeric interface for the central arcs. A geometric variance input
`A/768 ≤ V` yields the specific coefficient in the per-arc estimate. -/
theorem perArc_absolute_lower_of_variance {A V : ℝ} (hA : 1 ≤ A) (hV : A/768 ≤ V) :
    Real.sqrt A / 800 ≤ V/Real.sqrt (1+6*V) := by
  have hv : 0 ≤ V := by linarith
  have hq : 0 < Real.sqrt (1+6*V) := Real.sqrt_pos.mpr (by positivity)
  have hs := Real.sq_sqrt (show 0 ≤ A by linarith)
  have ht := Real.sq_sqrt (show 0 ≤ 1+6*V by positivity)
  have hb : A ≤ 768*V := by linarith
  have hquad : A*(1+6*V) ≤ (800*V)^2 := by
    nlinarith [mul_le_mul_of_nonneg_right hb (show 0 ≤ 1+6*V by positivity),
      mul_nonneg hv (show 0 ≤ 768*V-1 by linarith)]
  apply (le_div_iff₀ hq).mpr
  suffices H : Real.sqrt A * Real.sqrt (1+6*V) ≤ 800*V by linarith
  apply le_of_sq_le_sq _ (by positivity)
  simpa only [mul_pow, hs, ht] using (show A*(1+6*V) ≤ (800*V)^2 from hquad)

/-- The owner chooses the hit event using its actual sample. Once that
choice is fixed, its own coordinate contributes no hit. -/
theorem owner_selected_event_abs_lower {n : ℕ} {β : Fin n → Type*} [∀ i, Fintype (β i)]
    (w : ∀ i, β i → ℝ) (owner : Fin n) (event : β owner → ∀ i, β i → Bool)
    (hignore : ∀ a y, event a owner y = false)
    (hw0 : ∀ i y, 0 ≤ w i y) (hw : ∀ i, ∑ y, w i y = 1) (K : β owner → ℝ) :
    let p := fun a i => eventMarginal (w i) (event a i)
    let V := fun a => ∑ i, p a i * (1-p a i)
    mean (w owner) (fun a => V a / Real.sqrt (1+6*V a)) ≤ mean (productWeight w)
      (fun x => |(bitCount (fun i => event (x owner) i (x i)) : ℝ)-K (x owner)|) := by
  let F (a : β owner) (x : ∀ i, β i) := |(bitCount (fun i => event a i (x i)) : ℝ)-K a|
  have ignore (a : β owner) (x z : ∀ i, β i) (hxz : ∀ i, i ≠ owner → x i = z i) :
      F a x = F a z := by
    have indicators : (fun i => event a i (x i)) = (fun i => event a i (z i)) := by
      funext i
      by_cases hi : i = owner
      · subst i; simp only [hignore]
      · rw [hxz i hi]
    dsimp only [F]
    rw [indicators]
  apply le_trans _ (productWeight_owner_diagonal w owner (hw owner) F ignore).symm.le
  exact mean_mono_count (w owner) (hw0 owner) fun a =>
    product_event_count_abs_lower w (event a) hw0 hw (K a)

end Shellsort
end



