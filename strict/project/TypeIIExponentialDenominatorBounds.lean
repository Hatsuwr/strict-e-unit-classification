import TypeIISameMatrixDenominator
import BalancedIntegralTypeIIPade

/-! Numeric absorption for the literal Type-II lift matrix. No rank assertion. -/
noncomputable section
open scoped BigOperators NumberField
namespace StrictEUnit

def typeIILiftExponentialBase (r e : ℕ) (HT B C : ℝ) : ℝ :=
  2 * max 1 (2*(r:ℝ)^2*((r-1:ℕ)*e+1)*(((e+1)*HT)^(r-1))) *
    2^(2*r) * B * C^(4*r+2)

def typeIIDeterminantExponentialBase (r e τ : ℕ) (HT B C : ℝ) : ℝ :=
  max 1 ((r.factorial:ℝ)*(2*r+(r-1)*τ : ℕ)^r) * 2^r *
    (typeIILiftExponentialBase r e HT B C)^r

/-- A fixed prefactor and one polynomial parameter cost one fixed exponential base. -/
theorem typeII_fixed_factor_absorption (J X : ℝ) (hJ : 1 ≤ J) (hX : 0 ≤ X)
    (t : ℕ) (ht : 0 < t) : J*(t:ℝ)*X^t ≤ (2*J*X)^t := by
  have hnat : (t:ℝ) ≤ (2:ℝ)^t := by exact_mod_cast Nat.le_of_lt t.lt_two_pow_self
  have hpow : J ≤ J^t := le_self_pow₀ hJ (Nat.ne_of_gt ht)
  calc
    _ ≤ (J^t*(2:ℝ)^t)*X^t := mul_le_mul_of_nonneg_right
      (mul_le_mul hpow hnat (Nat.cast_nonneg _) (pow_nonneg (zero_le_one.trans hJ) _))
      (pow_nonneg hX _)
    _ = _ := by simp only [mul_pow]; ring

/-- One affine parameter covers the simultaneous-column cutoff and fixed threshold. -/
theorem typeII_affine_cutoff (r τ Z s : ℕ) (hr : 0 < r) :
    let a := r*(τ+1)+Z+1
    let t := a*(s+1)
    0 < t ∧ Z < t ∧ (s+r-1)*(τ+1) ≤ t := by
  dsimp only
  have hs : s+r-1 ≤ r*(s+1) := by
    have h : s ≤ r*s := by
      simpa only [one_mul] using Nat.mul_le_mul_right s (show 1 ≤ r from hr)
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hc := Nat.mul_le_mul_right (τ+1) hs
  have ha : r*(τ+1)*(s+1) ≤ (r*(τ+1)+Z+1)*(s+1) :=
    Nat.mul_le_mul_right _ (by omega)
  have hz : Z+1 ≤ (r*(τ+1)+Z+1)*(s+1) := by
    calc Z+1 ≤ r*(τ+1)+Z+1 := by omega
         _ ≤ (r*(τ+1)+Z+1)*(s+1) := Nat.le_mul_of_pos_right _ (by omega)
  refine ⟨by omega, by omega, ?_⟩
  calc (s+r-1)*(τ+1) ≤ r*(s+1)*(τ+1) := hc
       _ = r*(τ+1)*(s+1) := by ring
       _ ≤ _ := ha

/-- Absorb the exact sum used by the determinant House theorem. -/
theorem typeII_lift_bound_exponential (r e t : ℕ) (HT B C : ℝ)
    (hr : 0 < r) (ht : 0 < t) (hHT : 1 ≤ HT) (hB : 1 ≤ B) (hC : 1 ≤ C) :
    1 ≤ typeIILiftExponentialBase r e HT B C ∧
    typeIIIntegralLiftMatrixBound r e (2*r*t-1) HT (B^t)
      (C^(2*((2*r*t-1)+t+1))) ≤ (typeIILiftExponentialBase r e HT B C)^t := by
  let N := 2*r*t-1
  let AT : ℝ := (e+1)*HT
  let F : ℝ := ((r-1:ℕ)*e+1)*AT^(r-1)
  let J : ℝ := max 1 (2*(r:ℝ)^2*F)
  let X : ℝ := 2^(2*r)*B*C^(4*r+2)
  have hN : N+1 = 2*r*t := Nat.sub_add_cancel
    (Nat.succ_le_of_lt (Nat.mul_pos (Nat.mul_pos (by decide) hr) ht))
  have hAT : 1 ≤ AT := by dsimp [AT]; nlinarith [Nat.cast_nonneg (α:=ℝ) e]
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hJ : 1 ≤ J := le_max_left _ _
  have hX : 1 ≤ X := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hB) (one_le_pow₀ hC)
  have hbase : typeIILiftExponentialBase r e HT B C = 2*J*X := by
    dsimp [typeIILiftExponentialBase, J, F, AT, X]; ring
  refine ⟨?_, ?_⟩
  · rw [hbase]; exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by norm_num) hJ) hX
  have htail : (2:ℝ)^N*B^t*C^(2*(N+t+1)) ≤ X^t := by
    have hn : N ≤ (2*r)*t := by dsimp [N]; omega
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hn
    have he : 2*(N+t+1) = (4*r+2)*t := by nlinarith [hN]
    calc
      _ ≤ (2:ℝ)^((2*r)*t)*B^t*C^((4*r+2)*t) := by
        rw [he]; exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hp (by positivity)) (by positivity)
      _ = X^t := by dsimp [X]; simp only [mul_pow, ← pow_mul]
  have hterm (j : Fin r) :
      (j.val*e+1:ℝ)*AT^j.val*((N+1:ℝ)*2^N*B^t*C^(2*(N+t+1))) ≤
        F*(2*r*t:ℝ)*X^t := by
    have hj : j.val ≤ r-1 := by omega
    have hjR : (j.val:ℝ) ≤ ((r-1:ℕ):ℝ) := by exact_mod_cast hj
    have hfac : (j.val*e+1:ℝ)*AT^j.val ≤ F := by
      apply mul_le_mul (by nlinarith [Nat.cast_nonneg (α:=ℝ) e])
        (pow_le_pow_right₀ hAT hj) (pow_nonneg (zero_le_one.trans hAT) _) (by positivity)
    have hd : (N:ℝ)+1 = 2*r*t := by exact_mod_cast hN
    calc
      _ = ((j.val*e+1:ℝ)*AT^j.val)*(N+1)*
          (2^N*B^t*C^(2*(N+t+1))) := by ring
      _ ≤ F*(N+1)*X^t := mul_le_mul
          (mul_le_mul_of_nonneg_right hfac (by positivity)) htail (by positivity) (by positivity)
      _ = _ := by rw [hd]
  have hsum : typeIIIntegralLiftMatrixBound r e N HT (B^t)
      (C^(2*(N+t+1))) ≤ (2*(r:ℝ)^2*F)*(t:ℝ)*X^t := by
    unfold typeIIIntegralLiftMatrixBound
    calc
      _ ≤ ∑ j : Fin r, F*(2*r*t:ℝ)*X^t := Finset.sum_le_sum (fun j _ => hterm j)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  calc
    _ ≤ (2*(r:ℝ)^2*F)*(t:ℝ)*X^t := hsum
    _ ≤ J*(t:ℝ)*X^t := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg _)) (by positivity)
    _ ≤ (2*J*X)^t := typeII_fixed_factor_absorption J X hJ (zero_le_one.trans hX) t ht
    _ = _ := by rw [hbase]

/-- The exact determinant expression, not an assumed column bound. -/
theorem typeII_determinant_bound_exponential (r e τ t : ℕ) (HT B C : ℝ)
    (hr : 0 < r) (ht : 0 < t) (hHT : 1 ≤ HT) (hB : 1 ≤ B) (hC : 1 ≤ C) :
    1 ≤ typeIIDeterminantExponentialBase r e τ HT B C ∧
    (r.factorial:ℝ)*(((2*r*t-1+(r-1)*τ:ℕ)+1:ℝ)*
      typeIIIntegralLiftMatrixBound r e (2*r*t-1) HT (B^t)
        (C^(2*((2*r*t-1)+t+1))))^r ≤
      (typeIIDeterminantExponentialBase r e τ HT B C)^t := by
  let D := typeIILiftExponentialBase r e HT B C
  let L : ℝ := ((2*r+(r-1)*τ:ℕ):ℝ)
  let J : ℝ := max 1 ((r.factorial:ℝ)*L^r)
  obtain ⟨hD,hE⟩ := typeII_lift_bound_exponential r e t HT B C hr ht hHT hB hC
  have hJ : 1 ≤ J := le_max_left _ _
  have hG : typeIIDeterminantExponentialBase r e τ HT B C = J*2^r*D^r := rfl
  refine ⟨?_, ?_⟩
  · rw [hG]; exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hJ (one_le_pow₀ (by norm_num))) (one_le_pow₀ hD)
  have hN : 2*r*t-1+1 = 2*r*t := Nat.sub_add_cancel
    (Nat.succ_le_of_lt (Nat.mul_pos (Nat.mul_pos (by decide) hr) ht))
  have hd : (((2*r*t-1+(r-1)*τ:ℕ):ℝ)+1) ≤ L*(t:ℝ) := by
    have hz : (r-1)*τ ≤ (r-1)*τ*t := by
      simpa only [mul_one] using Nat.mul_le_mul_left ((r-1)*τ) (show 1 ≤ t from ht)
    dsimp [L]; push_cast
    have hnr : ((2*r*t-1:ℕ):ℝ)+1 = 2*r*t := by exact_mod_cast hN
    have hzr : (((r-1)*τ:ℕ):ℝ) ≤ (((r-1)*τ:ℕ):ℝ)*(t:ℝ) := by exact_mod_cast hz
    push_cast at hzr
    nlinarith
  have he0 : 0 ≤ typeIIIntegralLiftMatrixBound r e (2*r*t-1) HT (B^t)
      (C^(2*((2*r*t-1)+t+1))) := by unfold typeIIIntegralLiftMatrixBound; positivity
  have hnat : (t:ℝ) ≤ (2:ℝ)^t := by exact_mod_cast Nat.le_of_lt t.lt_two_pow_self
  have hpre : (r.factorial:ℝ)*L^r ≤ J^t :=
    (le_max_right _ _).trans (le_self_pow₀ hJ (Nat.ne_of_gt ht))
  calc
    _ ≤ (r.factorial:ℝ)*(L*(t:ℝ)*D^t)^r := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mul_nonneg (by positivity) he0)
        (mul_le_mul hd hE he0 (by dsimp [L]; positivity)) r) (by positivity)
    _ = ((r.factorial:ℝ)*L^r)*(t:ℝ)^r*(D^t)^r := by ring
    _ ≤ (J^t*((2:ℝ)^t)^r)*(D^t)^r := mul_le_mul_of_nonneg_right
      (mul_le_mul hpre (pow_le_pow_left₀ (Nat.cast_nonneg _) hnat r)
        (by positivity) (pow_nonneg (zero_le_one.trans hJ) _)) (by positivity)
    _ = _ := by rw [hG]; simp only [mul_pow, ← pow_mul]; rw [Nat.mul_comm t r]

end StrictEUnit
end
