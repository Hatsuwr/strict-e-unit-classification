import ExactImagePreimageArithmetic
import ExactImageZeroPreimageArithmetic
import RetainedActualCommonField
import Stage38SourceDifferentialTransport

noncomputable section
open scoped NumberField
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

/-- One common field, the exact retained amplitudes, and arithmetic preimages
for BOTH exponent classes. Integer exponents use the literal integer gauge. -/
theorem selectedFuchsSourceData_retained_family_preimage_arithmetic
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
          ((∀ z : ℤ,rhoE i≠(z:E)) →
            ∃ u : LaurentSeries (Polynomial E),
              (∃ h : ∀ m : ℕ,rhoE i+(m+1:ℕ)≠0,
                generalizedLogLaplaceLinear (rhoE i) h u=logPolynomialToCoefficientSeries (pE i)) ∧
              (∀ m,(u.coeff m).natDegree≤(pE i).natDegree) ∧ LogSeriesPrefixArithmetic u) ∧
          (∀ z : ℤ,rhoE i=(z:E) →
            ∃ u : LaurentSeries (Polynomial E),
              generalizedLogLaplaceLinear 0 logMixing_zero_forward_nonzero u=
                logPolynomialToCoefficientSeries (frobeniusIntegerShift z (pE i)) ∧
              (∀ m,(u.coeff m).natDegree≤(frobeniusIntegerShift z (pE i)).natDegree+1) ∧
              LogSeriesPrefixArithmetic u) := by
  let A := reciprocalSourceArray (n+1) (reciprocalCommonDegree (n+1) q) q
  obtain ⟨E,hE,psi,htower,AE,rhoE,pE,hA,hrE,hpE⟩ :=
    retainedFourierAmplitude_source_tower phi A hf e rho p hrho hp
  letI : FiniteDimensional ℚ E := hE
  letI : NumberField E := ⟨⟩
  have hsol (i) : actualTwistedStage53Action (rho i) A (p i)=0 := by
    rw [hrho,hp]
    exact sameFourierTwistedAmplitude_stage53 A hf hc (e.symm i)
  have hsolE (i) :
      let t := (T.map (algebraMap (𝓞 K) K)).map psi
      let U := fun i j =>((UI i j).map (algebraMap (𝓞 K) K)).map psi
      let qE := ordinaryReflectionTuple (n+1) (sameCompanionScalarTuple (n+1) (Nat.succ_pos n) t U)
      actualTwistedStage53Action (rhoE i)
        (reciprocalSourceArray (n+1) (reciprocalCommonDegree (n+1) qE) qE) (pE i)=0 := by
    apply actualRetained_source_tower_equation psi (algebraMap E AlgebraicComplex) phi htower
      (n+1) (Nat.succ_pos n) (T.map (algebraMap (𝓞 K) K))
      (fun i j =>(UI i j).map (algebraMap (𝓞 K) K)) (rhoE i) (rho i) (hrE i)
      (pE i) (p i) (hpE i)
    rw [← hq]
    exact hsol i
  refine ⟨E,hE,psi,htower,rhoE,pE,hrE,hpE,?_⟩
  intro i
  constructor
  · intro hni
    obtain ⟨u,hu,hd,ha⟩ := selectedFuchsSourceData_extended_actual_noninteger_preimage_arithmetic
      psi G a phi n hr c T UI B hsource (rhoE i) hni (pE i) (hsolE i)
    exact ⟨u,⟨_,hu⟩,hd,ha⟩
  · intro z hz
    apply selectedFuchsSourceData_extended_actual_zero_preimage_arithmetic
      psi G a phi n hr c T UI B hsource (frobeniusIntegerShift z (pE i))
    dsimp only
    rw [actualTwistedStage53Action_integerGauge,zero_add,← hz,hsolE i]
    simp only [frobeniusIntegerShift,mul_zero]
end StrictEUnit
end
