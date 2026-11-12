import ActualAmplitudeFactorialArithmetic

noncomputable section
open scoped NumberField
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

theorem selectedFuchsSourceData_retained_family_factorial_arithmetic
    (G : PowerSeries K) (a : ℕ →AlgebraicComplex) (phi : K →+* AlgebraicComplex)
    (n : ℕ) (hr : 0<n+1) (c : Fin (n+1) →RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (B : ℝ) (hsource : SelectedFuchsSourceData G a phi (n+1) hr c T UI B)
    (q : Fin (n+2) →Polynomial AlgebraicComplex)
    (hq : q=ordinaryReflectionTuple (n+1) (fun i =>
      (sameCompanionScalarTuple (n+1) (Nat.succ_pos n)
        (T.map (algebraMap (𝓞 K) K))
        (fun i j =>(UI i j).map (algebraMap (𝓞 K) K)) i).map phi))
    (hf : Stage56FiniteFuchs (reciprocalSourceArray (n+1) (reciprocalCommonDegree (n+1) q) q))
    (hc : (reciprocalSourceArray (n+1) (reciprocalCommonDegree (n+1) q) q)
      (Fin.last (n+1)) (Fin.last (reciprocalSourceDegree (n+1) (reciprocalCommonDegree (n+1) q) q))≠0)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols _ hf 0) ≃
      Fin (reciprocalSourceDegree (n+1) (reciprocalCommonDegree (n+1) q) q))
    (rho : Fin (reciprocalSourceDegree (n+1) (reciprocalCommonDegree (n+1) q) q) →AlgebraicComplex)
    (p : Fin (reciprocalSourceDegree (n+1) (reciprocalCommonDegree (n+1) q) q) →Polynomial (LaurentSeries AlgebraicComplex))
    (hrho : ∀ i,rho i=frobeniusRootSeedExponent _ (e.symm i))
    (hp : ∀ i,p i=sameFourierTwistedAmplitude _ hf (e.symm i)) :
    ∃ E : IntermediateField ℚ AlgebraicComplex,FiniteDimensional ℚ E ∧
      ∃ psi : K →+* E,(algebraMap E AlgebraicComplex).comp psi=phi ∧
      ∃ rhoE : _ →E,∃ pE : _ →Polynomial (LaurentSeries E),
        (∀ i,algebraMap E AlgebraicComplex (rhoE i)=rho i) ∧
        (∀ i,stage38_logMap (algebraMap E AlgebraicComplex) (pE i)=p i) ∧
        ∀ i,
          ((∀ z : ℤ,rhoE i≠(z:E)) →FactorialLogPrefixArithmetic (pE i)) ∧
          (∀ z : ℤ,rhoE i=(z:E) →FactorialLogPrefixArithmetic (frobeniusIntegerShift z (pE i))) := by
  obtain ⟨E,hE,psi,htower,rhoE,pE,hrE,hpE,hpre⟩ :=
    selectedFuchsSourceData_retained_family_preimage_arithmetic G a phi n hr c T UI B hsource
      q hq hf hc e rho p hrho hp
  letI : FiniteDimensional ℚ E := hE
  letI : NumberField E := ⟨⟩
  have hbin : JointBinomialPrefixDenominators rhoE := by
    apply selectedFuchsSourceData_lifted_exponent_binomial_arithmetic G a phi n hr c T UI B hsource
      q hq hf (algebraMap E AlgebraicComplex) rhoE
    intro i
    rw [hrE,hrho]
    exact frobeniusRootSeedExponent_isRoot _ _
  have hb0 := jointBinomialPrefixDenominators_adjoin_zero rhoE hbin
  refine ⟨E,hE,psi,htower,rhoE,pE,hrE,hpE,?_⟩
  intro i
  constructor
  · intro hni
    obtain ⟨u,⟨h,hu⟩,hd,ha⟩ := (hpre i).1 hni
    exact factorialLogPrefixArithmetic_of_preimage rhoE hbin i h (pE i) u _ hu hd ha
  · intro z hz
    obtain ⟨u,hu,hd,ha⟩ := (hpre i).2 z hz
    exact factorialLogPrefixArithmetic_of_preimage (fun j : Option _ =>j.elim 0 rhoE)
      hb0 none logMixing_zero_forward_nonzero (frobeniusIntegerShift z (pE i)) u _ hu hd ha
end StrictEUnit
end
