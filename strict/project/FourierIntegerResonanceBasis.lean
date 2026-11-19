import FrobeniusIntegerLiteralBasis

noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

def integerResonanceRootSeed (P : Polynomial K) (ξ : K)
    (i : polynomialLogIntegerResonanceIndex ξ P) : frobeniusRootSeedIndex P :=
  ⟨⟨ξ+(i.1.1 : K),by
    simpa only [polynomialIntegerResonanceIndices,Finset.mem_preimage] using i.1.2⟩,i.2⟩

theorem integerResonanceFrobeniusAmplitude_retained_fourier_index
    {μ ν : ℕ} (A : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs A)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin ν)
    (rho : Fin ν → K) (p : Fin ν → Polynomial (LaurentSeries K))
    (hrho : ∀ j,rho j = frobeniusRootSeedExponent _ (e.symm j))
    (hp : ∀ j,p j = sameFourierTwistedAmplitude A hf (e.symm j))
    (ξ : K) (i : polynomialLogIntegerResonanceIndex ξ
      (sameFourierEulerCoefficientSymbols A hf 0)) :
    ∃ j : Fin ν,rho j = ξ+(i.1.1 : K) ∧
      integerResonanceFrobeniusAmplitude (sameFourierEulerCoefficientSymbols A hf) ξ i =
        frobeniusIntegerShift i.1.1 (p j) := by
  let si := integerResonanceRootSeed (sameFourierEulerCoefficientSymbols A hf 0) ξ i
  refine ⟨e si,?_,?_⟩
  · rw [hrho,Equiv.symm_apply_apply]
    rfl
  · rw [hp,Equiv.symm_apply_apply]
    rfl

/-- One FIXED integer-resonance family is complete for BOTH full solution
spaces, with exact dimensions and unique expansions. The base exponent is
still external; nothing here asserts arithmetic or analytic convergence. -/
def FourierIntegerBasisData {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) : Prop :=
  ∀ hf : Stage56FiniteFuchs A,∀ ξ : K,
  let B := sameFourierEulerCoefficientSymbols A hf
  let b := fun k : Fin (ν+1) => (stage61_fourierLift A hf).coeff k.val
  FiniteDimensional K (polynomialLogLaurentSolutionSpace ν b ξ) ∧
  FiniteDimensional K (polynomialLogLiteralSolutionSpace ν b ξ) ∧
  Module.finrank K (polynomialLogLaurentSolutionSpace ν b ξ) = polynomialIntegerResonanceCost ξ (B 0) ∧
  Module.finrank K (polynomialLogLiteralSolutionSpace ν b ξ) = polynomialIntegerResonanceCost ξ (B 0) ∧
  polynomialIntegerResonanceCost ξ (B 0) ≤ ν ∧
  LinearIndependent K (integerResonanceFrobeniusAmplitude B ξ) ∧
  (∀ s : LaurentSeries (Polynomial K),scalarTwistedCoefficientOperator ν b ξ s = 0 →
    ∃! c : polynomialLogIntegerResonanceIndex ξ (B 0) → K,
      s = ∑ i,c i • integerResonanceFrobeniusCoefficients B ξ i) ∧
  (∀ p : Polynomial (LaurentSeries K),scalarTwistedLogOperator ν b ξ p = 0 →
    ∃! c : polynomialLogIntegerResonanceIndex ξ (B 0) → K,
      p = Fintype.linearCombination K (integerResonanceFrobeniusAmplitude B ξ) c) ∧
  ∀ e : frobeniusRootSeedIndex (B 0) ≃ Fin ν,
  ∀ rho : Fin ν → K,∀ p : Fin ν → Polynomial (LaurentSeries K),
    (∀ j,rho j = frobeniusRootSeedExponent _ (e.symm j)) →
    (∀ j,p j = sameFourierTwistedAmplitude A hf (e.symm j)) →
    ∀ i : polynomialLogIntegerResonanceIndex ξ (B 0),
      ∃ j : Fin ν,rho j = ξ+(i.1.1 : K) ∧
        integerResonanceFrobeniusAmplitude B ξ i = frobeniusIntegerShift i.1.1 (p j)

theorem fourierIntegerBasisData {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (hc : A (Fin.last μ) (Fin.last ν) ≠ 0) :
    FourierIntegerBasisData A := by
  intro hf ξ
  dsimp only
  have hP := sameFourierEulerIndicial_ne_zero A hf hc
  refine ⟨polynomialLogLaurentSolutionSpace_finiteDimensional ν _ ξ hP,
    Module.Finite.of_basis (integerResonanceLiteralBasis ν _ ξ hP),
    polynomialLogLaurentSolutionSpace_finrank_eq_integerResonanceCost ν _ ξ hP,
    polynomialLogLiteralSolutionSpace_finrank_eq_integerResonanceCost ν _ ξ hP,
    ?_,integerResonanceFrobeniusAmplitude_linearIndependent _ ξ,?_,?_,?_⟩
  · simpa only [sameFourierEulerIndicial_natDegree A hf hc] using
      polynomialIntegerResonanceCost_le ξ (sameFourierEulerCoefficientSymbols A hf 0)
  · intro s hs
    exact polynomialLogLaurentSolution_existsUnique_integer_expansion ν _ ξ hP s hs
  · intro p hp
    exact polynomialLogLiteralSolution_existsUnique_integer_expansion ν _ ξ hP p hp
  · intro e rho p hrho hp i
    exact integerResonanceFrobeniusAmplitude_retained_fourier_index A hf e rho p hrho hp ξ i

end StrictEUnit
end

#print axioms StrictEUnit.integerResonanceFrobeniusAmplitude_retained_fourier_index
#print axioms StrictEUnit.fourierIntegerBasisData
