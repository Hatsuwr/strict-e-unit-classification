import TwistedSelectedAmplitudeBridge

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]
attribute [local instance 2000] Algebra.toModule

theorem logPolynomial_coefficient_degree_bound (f : Polynomial (LaurentSeries K)) (n : ℤ) :
    ((logPolynomialToCoefficientSeries f).coeff n).natDegree≤f.natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [logPolynomialToCoefficientSeries_double_coeff,Polynomial.coeff_eq_zero_of_natDegree_lt hm]
  rfl

/-- Actual finite-log noninteger Fourier solutions have bounded homogeneous
source preimages; existence is proved, not supplied as an extra hypothesis. -/
theorem actualStage53_noninteger_source_exists {mu nu : ℕ} (rho : K)
    (hni : ∀ z : ℤ,rho≠(z:K)) (a : Fin (mu+1) → Fin (nu+1) → K)
    (f : Polynomial (LaurentSeries K)) (hf : actualTwistedStage53Action rho a f=0) :
    ∃ u : LaurentSeries (Polynomial K),
      generalizedLogLaplaceLinear rho (logMixing_noninteger_forward_nonzero rho hni) u=
        logPolynomialToCoefficientSeries f ∧
      generalizedLogSourceArrayAction rho a u=0 ∧
      (∀ n,(u.coeff n).natDegree≤f.natDegree) ∧
      (∀ n,(logPolynomialToCoefficientSeries f).coeff (n-1)=0 → u.coeff n=0) := by
  obtain ⟨u,hu,hd,hz⟩ := generalizedLogLaplaceSeries_noninteger_bounded_surjective rho hni
    (logPolynomialToCoefficientSeries f) f.natDegree (logPolynomial_coefficient_degree_bound f)
  refine ⟨u,hu,?_,hd,hz⟩
  exact (actualStage53_noninteger_source_iff rho hni a f u hu).mp hf

/-- The integer-normalized branch needs at most one additional log degree;
its source forcing is finite polynomial, not silently replaced by zero. -/
theorem actualStage53_zero_source_exists {mu nu : ℕ}
    (a : Fin (mu+1) → Fin (nu+1) → K)
    (f : Polynomial (LaurentSeries K)) (hf : actualTwistedStage53Action 0 a f=0) :
    ∃ u : LaurentSeries (Polynomial K),
      generalizedLogLaplaceLinear 0 logMixing_zero_forward_nonzero u=
        logPolynomialToCoefficientSeries f ∧
      (∀ n,(u.coeff n).natDegree≤f.natDegree+1) ∧
      (∀ n,(logPolynomialToCoefficientSeries f).coeff (n-1)=0 → u.coeff n=0) ∧
      ∃ P : Polynomial K,∀ k : ℤ,(generalizedLogSourceArrayAction 0 a u).coeff k=
        if k≤0 then Polynomial.C (P.coeff (-k).toNat) else 0 := by
  obtain ⟨u,hu,hd,hz⟩ := generalizedLogLaplaceSeries_zero_bounded_surjective
    (logPolynomialToCoefficientSeries f) f.natDegree (logPolynomial_coefficient_degree_bound f)
  exact ⟨u,hu,hd,hz,actualStage53_zero_source_residual a f u hu hf⟩

theorem sameFourierTwistedAmplitude_integer_stage53 {mu nu : ℕ}
    (a : Fin (mu+1) → Fin (nu+1) → K) (hf : Stage56FiniteFuchs a)
    (hc : a (Fin.last mu) (Fin.last nu)≠0)
    (i : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols a hf 0))
    (s : ℤ) (hs : frobeniusRootSeedExponent _ i=(s:K)) :
    actualTwistedStage53Action 0 a (frobeniusIntegerShift s (sameFourierTwistedAmplitude a hf i))=0 := by
  rw [actualTwistedStage53Action_integerGauge,zero_add,← hs,
    sameFourierTwistedAmplitude_stage53 a hf hc i,frobeniusIntegerShift,mul_zero]

end StrictEUnit
end
