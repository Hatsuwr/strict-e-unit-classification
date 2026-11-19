import FourierNaturalResonanceBasis
import SelectedFuchsSourceData

noncomputable section
open scoped BigOperators Matrix NumberField
namespace StrictEUnit

/-- Proven natural-resonance basis for the equation-defined nonnegative-power
coefficient solution space of the SAME selected Fourier operator. -/
def SameClearingFourierNaturalBasisData
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
  FourierNaturalBasisData A

theorem selectedFuchsSourceData_fourier_natural_basis
    {K : Type*} [Field K] [NumberField K]
    (G : PowerSeries K) (a : ℕ → AlgebraicComplex) (φ : K →+* AlgebraicComplex)
    (n : ℕ) (hr : 0<n+1) (c : Fin (n+1) → RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (E : ℝ) (hsource : SelectedFuchsSourceData G a φ (n+1) hr c T UI E) :
    SameClearingFourierNaturalBasisData φ n T UI := by
  obtain ⟨hdata,hT,hclear,htop,hqn,hann,hmin,hE,hden,hreg,hpTop,hpReg,
    hplusTop,hplusReg,hνeq,hνpos,hfinite,hcorner,hrest⟩ := hsource
  exact fourierNaturalBasisData _ hcorner

end StrictEUnit
end

#print axioms StrictEUnit.selectedFuchsSourceData_fourier_natural_basis
