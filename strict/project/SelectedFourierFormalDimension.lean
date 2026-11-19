import FrobeniusRepresentedCoefficientDetection
import FourierIndicialTwistedAmplitudes
import SelectedFuchsSourceData

noncomputable section
open scoped BigOperators Matrix NumberField
namespace StrictEUnit

/-- The full nonnegative-power formal solution space of the SAME Fourier
operator has injective resonant coordinates, is finite-dimensional, and has
dimension at most the actual resonance cost, itself at most Fourier order nu.
This is not a dimension assertion about arbitrary Laurent tails. -/
def FourierFormalDimensionData
    {K : Type*} [Field K] [CharZero K] {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) : Prop :=
  ∀ hf : Stage56FiniteFuchs A,∀ ξ : K,
    Function.Injective (polynomialLogResonanceCoordinates (sameFourierEulerCoefficientSymbols A hf) ξ) ∧
    FiniteDimensional K (polynomialLogFormalSolutionSpace (sameFourierEulerCoefficientSymbols A hf) ξ) ∧
    Module.finrank K (polynomialLogFormalSolutionSpace (sameFourierEulerCoefficientSymbols A hf) ξ) ≤
      polynomialResonanceTotalCost ξ (sameFourierEulerCoefficientSymbols A hf 0) ∧
    polynomialResonanceTotalCost ξ (sameFourierEulerCoefficientSymbols A hf 0) ≤ ν

theorem fourierFormalDimensionData
    {K : Type*} [Field K] [CharZero K] {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (hc : A (Fin.last μ) (Fin.last ν) ≠ 0) :
    FourierFormalDimensionData A := by
  intro hf ξ
  have hP := sameFourierEulerIndicial_ne_zero A hf hc
  refine ⟨polynomialLogResonanceCoordinates_injective _ ξ hP,
    polynomialLogFormalSolutionSpace_finiteDimensional _ ξ hP,
    polynomialLogFormalSolutionSpace_finrank_le_resonanceCost _ ξ hP,?_⟩
  exact (polynomialResonanceTotalCost_le ξ _).trans_eq
    (sameFourierEulerIndicial_natDegree A hf hc)

/-- The literal original tuple, reflection, reciprocal array and Fourier
order are unchanged. No solution space is defined by a constructed span. -/
def SameClearingFourierFormalDimensionData
    {K : Type*} [Field K] [NumberField K] (φ : K →+* AlgebraicComplex)
    (n : ℕ) (T : Polynomial (𝓞 K))
    (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K))) : Prop :=
  let t := T.map (algebraMap (𝓞 K) K)
  let U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K) :=
    fun i j => (UI i j).map (algebraMap (𝓞 K) K)
  let q := sameCompanionScalarTuple (n+1) (Nat.succ_pos n) t U
  let p : Fin (n+2) → Polynomial AlgebraicComplex := fun i => (q i).map φ
  let qplus := ordinaryReflectionTuple (n+1) p
  let d := reciprocalCommonDegree (n+1) qplus
  let A := reciprocalSourceArray (n+1) d qplus
  FourierFormalDimensionData A

theorem selectedFuchsSourceData_fourier_formal_dimension
    {K : Type*} [Field K] [NumberField K]
    (G : PowerSeries K) (a : ℕ → AlgebraicComplex) (φ : K →+* AlgebraicComplex)
    (n : ℕ) (hr : 0<n+1) (c : Fin (n+1) → RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (E : ℝ) (hsource : SelectedFuchsSourceData G a φ (n+1) hr c T UI E) :
    SameClearingFourierFormalDimensionData φ n T UI := by
  obtain ⟨hdata,hT,hclear,htop,hqn,hann,hmin,hE,hden,hreg,hpTop,hpReg,
    hplusTop,hplusReg,hνeq,hνpos,hfinite,hcorner,hrest⟩ := hsource
  exact fourierFormalDimensionData _ hcorner

end StrictEUnit
end

#print axioms StrictEUnit.fourierFormalDimensionData
#print axioms StrictEUnit.selectedFuchsSourceData_fourier_formal_dimension
