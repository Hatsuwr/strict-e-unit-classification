import RationalTwistedTopDerivative
import TwistedSelectedAmplitudeBridge
import Stage53FourierTupleNonzero

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem stage53_fourierCoeff_last_ne_zero {mu nu : ℕ}
    (A : Fin (mu+1) →Fin (nu+1) →K)
    (hc : A (Fin.last mu) (Fin.last nu)≠0) :
    stage53_fourierCoeff A (Fin.last nu)≠0 := by
  intro h
  have he := stage53_fourierCoeff_coeff_of_columns_above_zero A (Fin.last nu)
    (by intro i j hj;have := j.isLt; simp only [Fin.val_last] at hj;omega) (Fin.last mu)
  rw [h,Polynomial.coeff_zero] at he
  exact (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hc) he.symm

theorem sourceCoordinate_polynomial_rational (q : Polynomial K) :
    Polynomial.aeval (stage38_sourceCoordinate (K:=K) 1) q =
      Polynomial.C (algebraMap (RatFunc K) (LaurentSeries K)
        (algebraMap (Polynomial K) (RatFunc K) q)) := by
  rw [← IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) (LaurentSeries K)]
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add,map_add,Polynomial.C_add,hp,hq]
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [map_mul,map_pow,Polynomial.aeval_C,Polynomial.aeval_X,
      Polynomial.algebraMap_hahnSeries_apply,Polynomial.coe_C,Polynomial.coe_X,
      HahnSeries.ofPowerSeries_C,HahnSeries.ofPowerSeries_X]
    simp only [Polynomial.algebraMap_apply,LaurentSeries.algebraMap_apply,stage38_sourceCoordinate,Nat.cast_one]
end StrictEUnit
end
