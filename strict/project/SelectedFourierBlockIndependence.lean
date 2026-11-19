import FrobeniusAmplitudeBlockIndependence
import SelectedFourierJointBinomialArithmetic

noncomputable section
open scoped BigOperators Matrix NumberField
namespace StrictEUnit

/-- Independence in each fixed-exponent fiber of every exact indexing of the
SAME formal amplitudes. This does not assert independence between different
external exponents or a represented solution basis. -/
def FourierExactAmplitudeBlockIndependence
    {K : Type*} [Field K] [CharZero K] {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) : Prop :=
  ∀ hf : Stage56FiniteFuchs A,
  ∀ e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin ν,
  ∀ rho : Fin ν → K, ∀ p : Fin ν → Polynomial (LaurentSeries K),
    (∀ j,rho j = frobeniusRootSeedExponent _ (e.symm j)) →
    (∀ j,p j = sameFourierTwistedAmplitude A hf (e.symm j)) →
    ∀ ξ : K,LinearIndependent K (fun j : {j : Fin ν // rho j = ξ} => p j.1)

theorem fourierExactAmplitudeBlockIndependence
    {K : Type*} [Field K] [CharZero K] {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) :
    FourierExactAmplitudeBlockIndependence A := by
  intro hf e rho p hrho hp ξ
  exact sameFourierTwistedAmplitude_indexed_block_linearIndependent A hf e rho p hrho hp ξ

/-- The literal original source tuple, reflection, reciprocal array and
Fourier order are retained. No new annihilator or amplitude family is chosen. -/
def SameClearingFourierBlockIndependenceData
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
  FourierExactAmplitudeBlockIndependence A

theorem sameClearingFourierBlockIndependenceData
    {K : Type*} [Field K] [NumberField K] (φ : K →+* AlgebraicComplex)
    (n : ℕ) (T : Polynomial (𝓞 K))
    (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K))) :
    SameClearingFourierBlockIndependenceData φ n T UI := by
  exact fourierExactAmplitudeBlockIndependence _

end StrictEUnit
end

#print axioms StrictEUnit.fourierExactAmplitudeBlockIndependence
#print axioms StrictEUnit.sameClearingFourierBlockIndependenceData
