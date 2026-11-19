import ReciprocalGaugeCoefficients

/-! NEW SOURCE-ONLY, UNCOMPILED. Actual reciprocal coordinate and chain rule.
No arbitrary coordinate derivation or source-equation premise is introduced. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

def reciprocalGaugeZ : LaurentSeries K := HahnSeries.single (-1 : ℤ) (1 : K)
def reciprocalGaugeDz (y : LaurentSeries K) : LaurentSeries K :=
  HahnSeries.single (2 : ℤ) (-1 : K) * laurentOrdinaryDerivation y

theorem reciprocalGaugeZ_square : -(reciprocalGaugeZ (K := K))^2 =
    HahnSeries.single (-2 : ℤ) (-1 : K) := by
  ext n
  simp only [reciprocalGaugeZ, pow_two, HahnSeries.single_mul_single,
    show (-1 : ℤ)+(-1) = -2 by norm_num, one_mul,
    HahnSeries.coeff_neg, HahnSeries.coeff_single]
  split_ifs <;> ring

theorem reciprocalGaugeZ_derivative :
    laurentOrdinaryDerivation (reciprocalGaugeZ (K := K)) = -reciprocalGaugeZ^2 := by
  rw [reciprocalGaugeZ_square]
  ext n
  rw [laurentOrdinaryDerivation_coeff]
  simp only [reciprocalGaugeZ, HahnSeries.coeff_single]
  by_cases h : n = -2
  · subst n
    norm_num
  · have h' : n+1 ≠ -1 := by omega
    rw [if_neg h, if_neg h', mul_zero]

theorem reciprocalGauge_derivative_from_Dz (y : LaurentSeries K) :
    laurentOrdinaryDerivation y = -reciprocalGaugeZ^2 * reciprocalGaugeDz y := by
  rw [reciprocalGaugeZ_square]
  unfold reciprocalGaugeDz
  rw [← mul_assoc, HahnSeries.single_mul_single]
  norm_num only [neg_mul_neg, one_mul, HahnSeries.single_zero_one]

theorem reciprocalGauge_eval_derivative (P : Polynomial K) :
    laurentOrdinaryDerivation (Polynomial.aeval (reciprocalGaugeZ (K := K)) P) =
      Polynomial.aeval reciprocalGaugeZ (-(Polynomial.X^2) * Polynomial.derivative P) := by
  rw [Derivation.map_aeval, reciprocalGaugeZ_derivative]
  simp only [smul_eq_mul, map_mul, map_neg, map_pow, Polynomial.aeval_X]
  ring

/-- One exact normal-order step, retaining the genuine reciprocal D_z. -/
theorem reciprocalGauge_normal_step (P : Polynomial K) (y : LaurentSeries K) (k : ℕ) :
    laurentOrdinaryDerivation
      (Polynomial.aeval reciprocalGaugeZ P * reciprocalGaugeDz^[k] y) =
      Polynomial.aeval reciprocalGaugeZ (-(Polynomial.X^2) * Polynomial.derivative P) *
        reciprocalGaugeDz^[k] y +
      Polynomial.aeval reciprocalGaugeZ (-(Polynomial.X^2) * P) *
        reciprocalGaugeDz^[k+1] y := by
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  rw [reciprocalGauge_eval_derivative,
    reciprocalGauge_derivative_from_Dz (reciprocalGaugeDz^[k] y),
    Function.iterate_succ_apply']
  simp only [map_mul, map_neg, map_pow, Polynomial.aeval_X]
  ring

/-- Finite normal form after i original-variable derivatives. -/
def reciprocalGaugeAction (i : ℕ) (y : LaurentSeries K) : LaurentSeries K :=
  ∑ k ∈ Finset.range (i+1),
    Polynomial.aeval reciprocalGaugeZ (reciprocalGaugeCoefficient (K := K) i k) *
      reciprocalGaugeDz^[k] y

theorem reciprocalGaugeAction_derivative (i : ℕ) (y : LaurentSeries K) :
    laurentOrdinaryDerivation (reciprocalGaugeAction i y) =
      reciprocalGaugeAction (i+1) y := by
  let a (k : ℕ) : LaurentSeries K :=
    Polynomial.aeval reciprocalGaugeZ
      (-(Polynomial.X^2) * Polynomial.derivative (reciprocalGaugeCoefficient (K := K) i k)) *
        reciprocalGaugeDz^[k] y
  let b (k : ℕ) : LaurentSeries K :=
    Polynomial.aeval reciprocalGaugeZ (-(Polynomial.X^2) * reciprocalGaugeCoefficient (K := K) i k) *
      reciprocalGaugeDz^[k+1] y
  have ha : a (i+1) = 0 := by
    simp only [a, reciprocalGaugeCoefficient_above i (i+1) (by omega),
      map_zero, mul_zero, zero_mul]
  have hleft : laurentOrdinaryDerivation (reciprocalGaugeAction i y) =
      (∑ k ∈ Finset.range (i+1), a k) + ∑ k ∈ Finset.range (i+1), b k := by
    unfold reciprocalGaugeAction
    rw [map_sum]
    simp only [reciprocalGauge_normal_step, Finset.sum_add_distrib, a, b]
  have hright : reciprocalGaugeAction (i+1) y =
      (∑ k ∈ Finset.range (i+2), a k) +
        ∑ k ∈ Finset.range (i+2), if k=0 then 0 else b (k-1) := by
    unfold reciprocalGaugeAction
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [reciprocalGaugeCoefficient]
    by_cases hk0 : k=0
    · subst k
      simp only [if_pos rfl, if_true, mul_zero, sub_zero, a, add_zero]
    · have he : k-1+1=k := by omega
      simp only [if_neg hk0, a, b, he, map_sub, map_mul, map_neg,
        map_pow, Polynomial.aeval_X]
      ring
  have hfirst : (∑ k ∈ Finset.range (i+2), a k) = ∑ k ∈ Finset.range (i+1), a k := by
    rw [Finset.sum_range_succ, ha, add_zero]
  have hsecond : (∑ k ∈ Finset.range (i+2), if k=0 then 0 else b (k-1)) =
      ∑ k ∈ Finset.range (i+1), b k := by
    rw [Finset.sum_range_succ']
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false,
      Nat.add_sub_cancel, if_pos rfl, if_true, add_zero]
  rw [hleft, hright, hfirst, hsecond]

theorem reciprocalGauge_iterate (i : ℕ) (y : LaurentSeries K) :
    (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i]
      (reciprocalGaugeZ * y) = reciprocalGaugeAction i y := by
  induction i with
  | zero =>
    simp only [Function.iterate_zero_apply, reciprocalGaugeAction,
      Nat.zero_add, Finset.sum_range_one, reciprocalGaugeCoefficient,
      if_pos rfl, if_true, Polynomial.aeval_X, Function.iterate_zero_apply]
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, reciprocalGaugeAction_derivative]

/-- The reciprocal gauge really begins with G=z·(wG), including arbitrary
Laurent G, so the i=0 boundary is not an assumed normalization. -/
theorem reciprocalGauge_initial (G : LaurentSeries K) :
    reciprocalGaugeZ * (HahnSeries.single (1 : ℤ) (1 : K) * G) = G := by
  unfold reciprocalGaugeZ
  rw [← mul_assoc, HahnSeries.single_mul_single]
  norm_num only [one_mul, HahnSeries.single_zero_one]

end StrictEUnit
end
