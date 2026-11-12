import GeneralizedReciprocalResidualRecovery
import ReciprocalResidualLaurentForcing

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem logLaurentCoefficientMap_reciprocalW_pow (d : ℕ) :
    (logLaurentCoefficientMap (reciprocalGaugeW (K:=K)))^d=
      HahnSeries.single (d:ℤ) (1:Polynomial K) := by
  have hw : logLaurentCoefficientMap (reciprocalGaugeW (K:=K))=
      HahnSeries.single (1:ℤ) (1:Polynomial K) := by
    apply HahnSeries.ext
    funext n
    simp only [logLaurentCoefficientMap_coeff,reciprocalGaugeW,HahnSeries.coeff_single]
    split_ifs <;> simp
  rw [hw]
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ,ih,HahnSeries.single_mul_single]
    simp

/-- Actual noninteger Fourier preimages solve the SAME original ordinary source
operator, after the explicit reciprocal gauge is undone. -/
theorem actualStage53_noninteger_original_source_exists (rho : K)
    (hni : ∀ z : ℤ,rho≠(z:K)) (m : ℕ) (q : Fin (m+1) → Polynomial K)
    (f : Polynomial (LaurentSeries K))
    (hf : actualTwistedStage53Action rho
      (reciprocalSourceArray m (reciprocalCommonDegree m q) q) f=0) :
    ∃ u : LaurentSeries (Polynomial K),
      generalizedLogLaplaceLinear rho (logMixing_noninteger_forward_nonzero rho hni) u=
        logPolynomialToCoefficientSeries f ∧
      (∀ n,(u.coeff n).natDegree≤f.natDegree) ∧
      (∑ i,logLaurentCoefficientMap (Polynomial.aeval reciprocalGaugeW (q i))*
        (generalizedLogOrdinaryDerivative rho)^[i.val]
          (logLaurentCoefficientMap reciprocalGaugeZ*u))=0 := by
  obtain ⟨u,hu,hr,hd,hz⟩ := actualStage53_noninteger_source_exists rho hni _ f hf
  exact ⟨u,hu,hd,generalizedReciprocalSource_homogeneous rho m q u hr⟩

/-- Actual integer-normalized Fourier preimages solve the original ordinary
source operator with the explicitly recovered finite Laurent forcing d-j.
Negative forcing exponents are retained. -/
theorem actualStage53_zero_original_source_exists (m : ℕ) (q : Fin (m+1) → Polynomial K)
    (f : Polynomial (LaurentSeries K))
    (hf : actualTwistedStage53Action 0
      (reciprocalSourceArray m (reciprocalCommonDegree m q) q) f=0) :
    ∃ u : LaurentSeries (Polynomial K),
      generalizedLogLaplaceLinear 0 logMixing_zero_forward_nonzero u=
        logPolynomialToCoefficientSeries f ∧
      (∀ n,(u.coeff n).natDegree≤f.natDegree+1) ∧
      ∃ P : Polynomial K,
      (∑ i,logLaurentCoefficientMap (Polynomial.aeval reciprocalGaugeW (q i))*
        (generalizedLogOrdinaryDerivative 0)^[i.val]
          (logLaurentCoefficientMap reciprocalGaugeZ*u))=
        ∑ j : Fin (P.natDegree+1),HahnSeries.single
          ((reciprocalCommonDegree m q:ℤ)-(j.val:ℤ)) (Polynomial.C (P.coeff j.val)) := by
  obtain ⟨u,hu,hd,P,hP⟩ := actualStage53_zero_source_finite_laurent_forcing _ f hf
  refine ⟨u,hu,hd,P,?_⟩
  rw [generalizedReciprocalSource_residual_recovery,logLaurentCoefficientMap_reciprocalW_pow]
  exact hP _

end StrictEUnit
end
