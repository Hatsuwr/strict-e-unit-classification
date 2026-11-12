import TwistedLogStage53NormalOrder
import GeneralizedLogFourierArrayTransport
import FrobeniusIntegerShiftEquation

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]
attribute [local instance 2000] Algebra.toModule

theorem actualTwistedLogOrdinary_shiftedEuler (rho : K)
    (f : Polynomial (LaurentSeries K)) :
    actualTwistedLogOrdinary rho f=frobeniusIntegerShift (-1) (twistedLogPolynomialEuler rho f) := by
  change stage61_logOrdinaryDerivation 1 f+Polynomial.C (HahnSeries.single (-1 : ℤ) rho)*f=_
  rw [stage61_logOrdinaryDerivation_apply,stage38_sourceOrdinary_apply,
    stage38_sourceEuler_apply,twistedLogPolynomialEuler,frobeniusIntegerShift,
    stage61_logScalar_mul]
  simp only [Nat.cast_one,inv_one,← HahnSeries.C_apply,map_one,one_mul,mul_add]
  congr 1
  rw [← mul_assoc,← Polynomial.C_mul]
  congr 2
  simp only [HahnSeries.C_apply,HahnSeries.single_mul_single,add_zero,one_mul]

theorem logPolynomialToCoefficientSeries_frobeniusShift (a : ℤ)
    (f : Polynomial (LaurentSeries K)) :
    logPolynomialToCoefficientSeries (frobeniusIntegerShift a f)=
      HahnSeries.single a (1 : Polynomial K)*logPolynomialToCoefficientSeries f := by
  rw [frobeniusIntegerShift,map_mul,logPolynomialToCoefficientSeries_C]
  congr 1
  apply HahnSeries.ext
  funext n
  simp only [logLaurentCoefficientMap_coeff,HahnSeries.coeff_single]
  split_ifs <;> simp

/-- The concrete Stage53 twisted derivative is EXACTLY the derivative in
the already checked generalized transform, after the fixed ring embedding. -/
theorem actualTwistedLogOrdinary_coefficient_bridge (rho : K)
    (f : Polynomial (LaurentSeries K)) :
    logPolynomialToCoefficientSeries (actualTwistedLogOrdinary rho f)=
      -logTargetNegativeDerivative rho (logPolynomialToCoefficientSeries f) := by
  rw [actualTwistedLogOrdinary_shiftedEuler,logPolynomialToCoefficientSeries_frobeniusShift,
    logPolynomialToCoefficientSeries_twistedEuler,logTargetNegativeDerivative,neg_neg]
  congr 1
  apply HahnSeries.ext
  funext n
  rw [twistedPolynomialCoefficientEuler_coeff]
  rfl

end StrictEUnit
end
