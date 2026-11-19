import ActualFourierFieldDescent

noncomputable section
namespace StrictEUnit

/-- Exact retained solutions over ONE common finite field, including their
actual Stage53 equation. The original source field may be included via F. -/
theorem retainedFourier_actual_common_field {mu nu : ℕ}
    (A : Fin (mu+1) →Fin (nu+1) →AlgebraicComplex)
    (hf : Stage56FiniteFuchs A) (hc : A (Fin.last mu) (Fin.last nu)≠0)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin nu)
    (rho : Fin nu →AlgebraicComplex) (p : Fin nu →Polynomial (LaurentSeries AlgebraicComplex))
    (hrho : ∀ j,rho j=frobeniusRootSeedExponent _ (e.symm j))
    (hp : ∀ j,p j=sameFourierTwistedAmplitude A hf (e.symm j))
    (F : IntermediateField ℚ AlgebraicComplex) (hF : FiniteDimensional ℚ F) :
    ∃ E : IntermediateField ℚ AlgebraicComplex,FiniteDimensional ℚ E ∧ F≤E ∧
      ∃ AE : Fin (mu+1) →Fin (nu+1) →E,∃ rhoE : Fin nu →E,
      ∃ pE : Fin nu →Polynomial (LaurentSeries E),
        (∀ i j,algebraMap E AlgebraicComplex (AE i j)=A i j) ∧
        (∀ i,algebraMap E AlgebraicComplex (rhoE i)=rho i) ∧
        (∀ i,stage38_logMap (algebraMap E AlgebraicComplex) (pE i)=p i) ∧
        ∀ i,actualTwistedStage53Action (rhoE i) AE (pE i)=0 := by
  obtain ⟨E,hE,hFE,AE,rhoE,pE,hA,hr,hpE⟩ :=
    retainedFourierAmplitude_exact_common_field A hf e rho p hrho hp F hF
  refine ⟨E,hE,hFE,AE,rhoE,pE,hA,hr,hpE,?_⟩
  intro i
  apply (actualTwistedStage53Action_field_iff (algebraMap E AlgebraicComplex) (rhoE i) AE (pE i)).mp
  simp only [hr,hpE,hA,hrho,hp]
  exact sameFourierTwistedAmplitude_stage53 A hf hc (e.symm i)

/-- Branchwise preimages exist over that same field: noninteger branches are
homogeneous, integer branches are normalized by their literal integer shift
and retain the finite residual polynomial. No arithmetic conclusion is added. -/
theorem actualFiniteFamily_common_field_preimages
    {K : Type*} [Field K] [CharZero K] {ι : Type*} {mu nu : ℕ}
    (A : Fin (mu+1) →Fin (nu+1) →K) (rho : ι →K)
    (p : ι →Polynomial (LaurentSeries K))
    (hp : ∀ i,actualTwistedStage53Action (rho i) A (p i)=0) :
    ∀ i,
      ((∀ z : ℤ,rho i≠(z:K)) →
        ∃ u : LaurentSeries (Polynomial K),
          (∃ h : ∀ n : ℕ,rho i+(n+1:ℕ)≠0,
            generalizedLogLaplaceLinear (rho i) h u=logPolynomialToCoefficientSeries (p i)) ∧
          generalizedLogSourceArrayAction (rho i) A u=0 ∧
          ∀ n,(u.coeff n).natDegree≤(p i).natDegree) ∧
      (∀ z : ℤ,rho i=(z:K) →
        ∃ u : LaurentSeries (Polynomial K),
          generalizedLogLaplaceLinear 0 logMixing_zero_forward_nonzero u=
            logPolynomialToCoefficientSeries (frobeniusIntegerShift z (p i)) ∧
          ∃ P : Polynomial K,∀ k : ℤ,(generalizedLogSourceArrayAction 0 A u).coeff k=
            if k≤0 then Polynomial.C (P.coeff (-k).toNat) else 0) := by
  intro i
  constructor
  · intro hni
    obtain ⟨u,hu,hs,hd,hz⟩ := actualStage53_noninteger_source_exists (rho i) hni A (p i) (hp i)
    exact ⟨u,⟨_,hu⟩,hs,hd⟩
  · intro z hz
    have hs : actualTwistedStage53Action 0 A (frobeniusIntegerShift z (p i))=0 := by
      rw [actualTwistedStage53Action_integerGauge,zero_add,← hz,hp i]
      simp [frobeniusIntegerShift]
    obtain ⟨u,hu,hd,hzero,P,hP⟩ := actualStage53_zero_source_exists A _ hs
    exact ⟨u,hu,P,hP⟩

end StrictEUnit
end
