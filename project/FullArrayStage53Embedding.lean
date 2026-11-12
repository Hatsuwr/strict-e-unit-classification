import TwistedLogOrdinaryCoefficientBridge

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]
attribute [local instance 2000] Algebra.toModule

theorem actualTwistedLogOrdinary_signed_iterate (rho : K) (n : ℕ)
    (f : Polynomial (LaurentSeries K)) :
    logPolynomialToCoefficientSeries ((-1 : K)^n • (actualTwistedLogOrdinary rho)^[n] f)=
      (logTargetNegativeDerivative rho)^[n] (logPolynomialToCoefficientSeries f) := by
  induction n with
  | zero => simp [Algebra.smul_def]
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hs : (-1 : K)^(n+1) • actualTwistedLogOrdinary rho ((actualTwistedLogOrdinary rho)^[n] f)=
        -actualTwistedLogOrdinary rho ((-1 : K)^n • (actualTwistedLogOrdinary rho)^[n] f) := by
      rw [map_smul,pow_succ]
      simp only [Algebra.smul_def,map_mul,map_neg,map_one]
      ring
    rw [hs,map_neg,actualTwistedLogOrdinary_coefficient_bridge,neg_neg,ih,
      Function.iterate_succ_apply']

theorem logPolynomialToCoefficientSeries_coordinate_mul (f : Polynomial (LaurentSeries K)) :
    logPolynomialToCoefficientSeries (stage38_sourceCoordinate (K:=K) 1*f)=
      logTargetX (logPolynomialToCoefficientSeries f) := by
  exact logPolynomialToCoefficientSeries_frobeniusShift 1 f

theorem logPolynomialToCoefficientSeries_coordinate_pow (n : ℕ)
    (f : Polynomial (LaurentSeries K)) :
    logPolynomialToCoefficientSeries ((stage38_sourceCoordinate (K:=K) 1)^n*f)=
      logTargetX^[n] (logPolynomialToCoefficientSeries f) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',mul_assoc,logPolynomialToCoefficientSeries_coordinate_mul,ih,
      Function.iterate_succ_apply']

/-- Exact full-array embedding into the existing Stage53 normal-ordered tuple. -/
theorem generalizedLogFourierArrayAction_stage53 {mu nu : ℕ} (rho : K)
    (a : Fin (mu+1) → Fin (nu+1) → K) (f : Polynomial (LaurentSeries K)) :
    generalizedLogFourierArrayAction rho a (logPolynomialToCoefficientSeries f)=
      logPolynomialToCoefficientSeries
        (∑ l,Polynomial.aeval (stage38_sourceCoordinate (K:=K) 1) (stage53_fourierCoeff a l)*
          (actualTwistedLogOrdinary rho)^[l.val] f) := by
  rw [← actualTwistedLogOrdinary_stage53]
  simp only [generalizedLogFourierArrayAction,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [← logPolynomialToCoefficientSeries_coordinate_pow,
    ← actualTwistedLogOrdinary_signed_iterate]
  rw [← logPolynomialToCoefficientSeries_smul]
  congr 1
  simp only [Algebra.smul_def,map_mul]
  ring

end StrictEUnit
end
