import GeneralizedLogOrdinaryProduct

noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem logLaurentCoefficientMap_reciprocalZ :
    logLaurentCoefficientMap (reciprocalGaugeZ (K:=K))=HahnSeries.single (-1:ℤ) (1:Polynomial K) := by
  apply HahnSeries.ext
  funext n
  simp only [logLaurentCoefficientMap_coeff,reciprocalGaugeZ,HahnSeries.coeff_single]
  split_ifs <;> simp

theorem generalizedReciprocalGauge_derivative_from_Dz (rho : K)
    (y : LaurentSeries (Polynomial K)) :
    generalizedLogOrdinaryDerivative rho y=
      -(logLaurentCoefficientMap (reciprocalGaugeZ (K:=K)))^2*reciprocalLogSeriesDerivative rho y := by
  rw [generalizedLogOrdinaryDerivative_from_reciprocal,logLaurentCoefficientMap_reciprocalZ]
  rw [pow_two,HahnSeries.single_mul_single]
  norm_num [neg_mul]
  ring

/-- One exact normal-order step, retaining the genuine reciprocal D_z. -/
theorem generalizedReciprocalGauge_normal_step (rho : K) (P : Polynomial K) (y : LaurentSeries (Polynomial K)) (k : ℕ) :
    generalizedLogOrdinaryDerivative rho
      (logLaurentCoefficientMap (Polynomial.aeval reciprocalGaugeZ P) * (reciprocalLogSeriesDerivative rho)^[k] y) =
      logLaurentCoefficientMap (Polynomial.aeval reciprocalGaugeZ (-(Polynomial.X^2) * Polynomial.derivative P)) *
        (reciprocalLogSeriesDerivative rho)^[k] y +
      logLaurentCoefficientMap (Polynomial.aeval reciprocalGaugeZ (-(Polynomial.X^2) * P)) *
        (reciprocalLogSeriesDerivative rho)^[k+1] y := by
  rw [generalizedLogOrdinaryDerivative_logfree_mul]
  rw [reciprocalGauge_eval_derivative,
    generalizedReciprocalGauge_derivative_from_Dz rho ((reciprocalLogSeriesDerivative rho)^[k] y),
    Function.iterate_succ_apply']
  simp only [map_mul, map_neg, map_pow, Polynomial.aeval_X]
  ring

/-- Finite normal form after i original-variable derivatives. -/
def generalizedReciprocalGaugeAction (rho : K) (i : ℕ) (y : LaurentSeries (Polynomial K)) : LaurentSeries (Polynomial K) :=
  ∑ k ∈ Finset.range (i+1),
    logLaurentCoefficientMap (Polynomial.aeval reciprocalGaugeZ (reciprocalGaugeCoefficient (K := K) i k)) *
      (reciprocalLogSeriesDerivative rho)^[k] y

theorem generalizedReciprocalGaugeAction_derivative (rho : K) (i : ℕ) (y : LaurentSeries (Polynomial K)) :
    generalizedLogOrdinaryDerivative rho (generalizedReciprocalGaugeAction rho i y) =
      generalizedReciprocalGaugeAction rho (i+1) y := by
  let a (k : ℕ) : LaurentSeries (Polynomial K) :=
    logLaurentCoefficientMap (Polynomial.aeval reciprocalGaugeZ
      (-(Polynomial.X^2) * Polynomial.derivative (reciprocalGaugeCoefficient (K := K) i k))) *
        (reciprocalLogSeriesDerivative rho)^[k] y
  let b (k : ℕ) : LaurentSeries (Polynomial K) :=
    logLaurentCoefficientMap (Polynomial.aeval reciprocalGaugeZ (-(Polynomial.X^2) * reciprocalGaugeCoefficient (K := K) i k)) *
      (reciprocalLogSeriesDerivative rho)^[k+1] y
  have ha : a (i+1) = 0 := by
    simp only [a, reciprocalGaugeCoefficient_above i (i+1) (by omega),
      map_zero, mul_zero, zero_mul]
  have hleft : generalizedLogOrdinaryDerivative rho (generalizedReciprocalGaugeAction rho i y) =
      (∑ k ∈ Finset.range (i+1), a k) + ∑ k ∈ Finset.range (i+1), b k := by
    unfold generalizedReciprocalGaugeAction
    change generalizedLogOrdinaryDerivativeAdd rho (∑ k ∈ Finset.range (i+1), _) = _
    rw [map_sum]
    change (∑ k ∈ Finset.range (i+1),generalizedLogOrdinaryDerivative rho _) = _
    simp only [generalizedReciprocalGauge_normal_step, Finset.sum_add_distrib, a, b]
  have hright : generalizedReciprocalGaugeAction rho (i+1) y =
      (∑ k ∈ Finset.range (i+2), a k) +
        ∑ k ∈ Finset.range (i+2), if k=0 then 0 else b (k-1) := by
    unfold generalizedReciprocalGaugeAction
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

theorem generalizedReciprocalGauge_iterate (rho : K) (i : ℕ) (y : LaurentSeries (Polynomial K)) :
    (generalizedLogOrdinaryDerivative rho)^[i]
      (logLaurentCoefficientMap reciprocalGaugeZ * y) = generalizedReciprocalGaugeAction rho i y := by
  induction i with
  | zero =>
    simp only [Function.iterate_zero_apply, generalizedReciprocalGaugeAction,
      Nat.zero_add, Finset.sum_range_one, reciprocalGaugeCoefficient,
      if_pos rfl, if_true, Polynomial.aeval_X, Function.iterate_zero_apply]
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, generalizedReciprocalGaugeAction_derivative]


end StrictEUnit
end
