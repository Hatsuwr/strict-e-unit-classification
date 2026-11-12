import GeneralizedReciprocalSourceIdentity

noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Undoing the reciprocal gauge recovers the exact original source residual,
including arbitrary logarithms and external exponent rho. -/
theorem generalizedReciprocalSource_residual_recovery (rho : K) (m : ℕ)
    (q : Fin (m+1) → Polynomial K) (y : LaurentSeries (Polynomial K)) :
    (∑ i,logLaurentCoefficientMap (Polynomial.aeval reciprocalGaugeW (q i))*
      (generalizedLogOrdinaryDerivative rho)^[i.val]
        (logLaurentCoefficientMap reciprocalGaugeZ*y))=
      (logLaurentCoefficientMap (reciprocalGaugeW (K:=K)))^(reciprocalCommonDegree m q)*
        generalizedLogSourceArrayAction rho
          (reciprocalSourceArray m (reciprocalCommonDegree m q) q) y := by
  have hinv : logLaurentCoefficientMap (reciprocalGaugeW (K:=K))*
      logLaurentCoefficientMap reciprocalGaugeZ=1 := by
    rw [← map_mul,mul_comm,reciprocalGauge_inverse,map_one]
  have hy : logLaurentCoefficientMap reciprocalGaugeW*(logLaurentCoefficientMap reciprocalGaugeZ*y)=y := by
    rw [← mul_assoc,hinv,one_mul]
  have h := generalizedReciprocalSourceArray_action_identity rho m q
    (logLaurentCoefficientMap reciprocalGaugeZ*y)
  rw [hy] at h
  rw [h,← mul_assoc,← mul_pow,hinv,one_pow,one_mul]

/-- A genuinely zero reciprocal residual gives the original homogeneous source
ODE, without imposing it as an extra premise on the chosen preimage. -/
theorem generalizedReciprocalSource_homogeneous (rho : K) (m : ℕ)
    (q : Fin (m+1) → Polynomial K) (y : LaurentSeries (Polynomial K))
    (hy : generalizedLogSourceArrayAction rho
      (reciprocalSourceArray m (reciprocalCommonDegree m q) q) y=0) :
    (∑ i,logLaurentCoefficientMap (Polynomial.aeval reciprocalGaugeW (q i))*
      (generalizedLogOrdinaryDerivative rho)^[i.val]
        (logLaurentCoefficientMap reciprocalGaugeZ*y))=0 := by
  rw [generalizedReciprocalSource_residual_recovery,hy,mul_zero]

end StrictEUnit
end
