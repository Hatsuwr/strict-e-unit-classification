import FourierResonanceClassSolutions
import SelectedFuchsSourceData

noncomputable section
open scoped BigOperators Matrix NumberField
namespace StrictEUnit

/-- Every integral resonance class of the SAME selected Fourier amplitudes
is independent over the coefficient field and solves a common twisted
operator after its derived integer shifts. Base exponents remain external. -/
def SameClearingFourierResonanceSolutionData
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
  FourierExactResonanceSolutionData A

/-- The necessary nonzero Fourier corner comes from the original source
packet. No extra rank, family, spectrum or integer-shift premise is added. -/
theorem selectedFuchsSourceData_fourier_resonance_solutions
    {K : Type*} [Field K] [NumberField K]
    (G : PowerSeries K) (a : ℕ → AlgebraicComplex) (φ : K →+* AlgebraicComplex)
    (n : ℕ) (hr : 0<n+1) (c : Fin (n+1) → RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (E : ℝ) (hsource : SelectedFuchsSourceData G a φ (n+1) hr c T UI E) :
    SameClearingFourierResonanceSolutionData φ n T UI := by
  obtain ⟨hdata,hT,hclear,htop,hqn,hann,hmin,hE,hden,hreg,hpTop,hpReg,
    hplusTop,hplusReg,hνeq,hνpos,hfinite,hcorner,hrest⟩ := hsource
  exact fourierExactResonanceSolutionData _ hcorner

end StrictEUnit
end

#print axioms StrictEUnit.selectedFuchsSourceData_fourier_resonance_solutions
