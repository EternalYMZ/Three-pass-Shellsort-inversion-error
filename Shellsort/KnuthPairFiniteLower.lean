import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic

/-! Algebraic estimates on the classical finite pair formula. Identification
with the inversion expectation is a separate combinatorial theorem. -/
noncomputable section
namespace Shellsort.KnuthPairFiniteLower

private theorem binomial_square (t : ℕ) :
    ((t:ℝ)+1)*(t.centralBinom:ℝ)^2 ≤ ((4:ℝ)^t)^2 := by
  induction t with
  | zero => norm_num [Nat.centralBinom_zero]
  | succ t ih =>
    have recurrence : ((t:ℝ)+1)*((t+1).centralBinom:ℝ) =
        2*(2*(t:ℝ)+1)*(t.centralBinom:ℝ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ t
    have coeff : ((t:ℝ)+2)*(2*(2*(t:ℝ)+1))^2 ≤ (((t:ℝ)+1)^2*16)*((t:ℝ)+1) := by
      nlinarith [sq_nonneg (t:ℝ),Nat.cast_nonneg (α:=ℝ) t]
    have scale := mul_le_mul_of_nonneg_right coeff (sq_nonneg (t.centralBinom:ℝ))
    have prior := mul_le_mul_of_nonneg_left ih
      (show 0 ≤ ((t:ℝ)+1)^2*16 by positivity)
    push_cast
    apply (mul_le_mul_iff_right₀ (show (0:ℝ)<((t:ℝ)+1)^2 by positivity)).mp
    rw [pow_succ (4:ℝ) t]
    have e := congrArg (fun z : ℝ => ((t:ℝ)+2)*z^2) recurrence
    nlinarith only [scale,prior,e]

def equalPair (t : ℕ) : ℝ := t * (4:ℝ)^t / (4*t.centralBinom)
def unequalPair (t : ℕ) : ℝ := (2*((t:ℝ)+1)/(2*t+1)) * equalPair t
def pairCount (x : ℝ) : ℝ := x*(x-1)/2

def finiteMean (d t j : ℕ) :=
  pairCount ((d:ℝ)-j) * equalPair t +
  (j:ℝ)*((d:ℝ)-j) * unequalPair t + pairCount (j:ℝ) * equalPair (t+1)

private theorem equal_lower (t : ℕ) :
    (t:ℝ)*Real.sqrt t/4 ≤ equalPair t := by
  have c : (0:ℝ)<t.centralBinom := by exact_mod_cast Nat.centralBinom_pos t
  have small : (Real.sqrt (t:ℝ)*(t.centralBinom:ℝ))^2 ≤ ((4:ℝ)^t)^2 := by
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
    nlinarith only [binomial_square t,sq_nonneg (t.centralBinom:ℝ)]
  have rt := (sq_le_sq₀ (by positivity) (by positivity)).mp small
  unfold equalPair
  apply (le_div_iff₀ (show (0:ℝ)<4*t.centralBinom by positivity)).mpr
  nlinarith only [mul_le_mul_of_nonneg_left rt (Nat.cast_nonneg (α:=ℝ) t)]

private theorem pair_nonneg (s : ℕ) : 0 ≤ pairCount (s:ℝ) := by
  cases s with
  | zero => norm_num [pairCount]
  | succ s => simp [pairCount]; positivity

theorem finite_lower {d t j : ℕ} (hd : 2≤d) (ht : 1≤t) (hj : j<d) :
    let m : ℝ := (d:ℝ)*t+j
    m*Real.sqrt m/32 ≤ finiteMean d t j := by
  let s : ℝ := (t:ℝ)*Real.sqrt t/4
  have dR : (2:ℝ) ≤ d := by exact_mod_cast hd
  have tR : (1:ℝ) ≤ t := by exact_mod_cast ht
  have jR : (j:ℝ)+1 ≤ d := by exact_mod_cast hj
  have x : 0 ≤ pairCount ((d:ℝ)-j) := by
    unfold pairCount
    exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
  have y : 0 ≤ (j:ℝ)*((d:ℝ)-j) := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have a : s ≤ equalPair t := equal_lower t
  have al : 0 ≤ equalPair t := (by dsimp [s]; positivity : 0 ≤ s).trans a
  have b : s ≤ unequalPair t := by
    unfold unequalPair
    apply a.trans
    apply le_mul_of_one_le_left al
    apply (le_div_iff₀ (by positivity)).mpr
    linarith
  have c : s ≤ equalPair (t+1) := by
    apply le_trans _ (equal_lower (t+1))
    dsimp [s]
    gcongr <;> exact_mod_cast Nat.le_succ t
  have bound : pairCount d * s ≤ finiteMean d t j := by
    calc
      _ = pairCount ((d:ℝ)-j)*s + (j:ℝ)*((d:ℝ)-j)*s + pairCount j*s := by unfold pairCount; ring
      _ ≤ _ := add_le_add (add_le_add (mul_le_mul_of_nonneg_left a x)
        (mul_le_mul_of_nonneg_left b y)) (mul_le_mul_of_nonneg_left c (pair_nonneg j))
  apply le_trans _ bound
  dsimp [pairCount,s]
  have rt : Real.sqrt ((d:ℝ)*t+j) ≤ 2*((d:ℝ)-1)*Real.sqrt t := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact mul_nonneg (by linarith) (Real.sqrt_nonneg _)
    · rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
      have w : 2*(d:ℝ) ≤ (2*((d:ℝ)-1))^2 := by
        nlinarith only [mul_nonneg (show 0≤(d:ℝ)-2 by linarith) (show 0≤4*(d:ℝ)-2 by linarith)]
      nlinarith only [mul_le_mul_of_nonneg_right w (Nat.cast_nonneg (α:=ℝ) t),
        mul_le_mul_of_nonneg_left tR (Nat.cast_nonneg (α:=ℝ) d),jR]
  have m : (d:ℝ)*t+j ≤ 2*(d:ℝ)*t := by
    nlinarith only [mul_le_mul_of_nonneg_left tR (Nat.cast_nonneg (α:=ℝ) d),jR]
  nlinarith only [mul_le_mul m rt (Real.sqrt_nonneg _) (by positivity)]

#print axioms finite_lower
end Shellsort.KnuthPairFiniteLower
