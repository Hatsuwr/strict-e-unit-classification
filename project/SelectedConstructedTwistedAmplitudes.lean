import FourierFiniteTwistedAmplitudes
import SelectedEulerPowerSeriesCoefficients
import SelectedFuchsSourceData

noncomputable section
open scoped BigOperators Matrix NumberField
namespace StrictEUnit

/-- The SAME reciprocal array as the selected source packet, with counted
formal twisted amplitudes of Fourier order nu. Source order r is unchanged. -/
def SelectedFourierTwistedAmplitudeData
    {K : Type*} [Field K] [NumberField K] (φ : K →+* AlgebraicComplex)
    (r : ℕ) (hr : 0<r) (T : Polynomial (𝓞 K))
    (UI : Matrix (Fin r) (Fin r) (Polynomial (𝓞 K))) : Prop :=
  let t := T.map (algebraMap (𝓞 K) K)
  let U : Matrix (Fin r) (Fin r) (Polynomial K) :=
    Matrix.of (fun i j => (UI i j).map (algebraMap (𝓞 K) K))
  let qF := sameCompanionScalarTuple r hr t U
  let p : Fin (r+1) → Polynomial AlgebraicComplex := fun i => (qF i).map φ
  let qplus := ordinaryReflectionTuple r p
  let d := reciprocalCommonDegree r qplus
  let A := reciprocalSourceArray r d qplus
  FourierFiniteTwistedAmplitudeData A

theorem selectedFuchsSourceData_constructed_twisted_amplitudes
    {K : Type*} [Field K] [NumberField K]
    (G : PowerSeries K) (a : ℕ → AlgebraicComplex) (φ : K →+* AlgebraicComplex)
    (r : ℕ) (hr : 0<r) (c : Fin r → RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin r) (Fin r) (Polynomial (𝓞 K)))
    (E : ℝ) (hsource : SelectedFuchsSourceData G a φ r hr c T UI E) :
    SelectedFourierTwistedAmplitudeData φ r hr T UI := by
  obtain ⟨hdata,hT,hclear,htop,hqn,hann,hmin,hE,hden,hreg,hpTop,hpReg,
    hplusTop,hplusReg,hνeq,hνpos,hfinite,hcorner,hrest⟩ := hsource
  letI : IsAlgClosed AlgebraicComplex := IsAlgClosure.isAlgClosed ℚ
  exact exists_fourierFiniteTwistedAmplitudeData _ hfinite hcorner

/-- The original packet derives the regular source Euler coefficient matrix
and the literal residue identity, including the ordinary-origin case. -/
theorem selectedFuchsSourceData_regularEuler_coefficients
    {K : Type*} [Field K] [NumberField K]
    (G : PowerSeries K) (a : ℕ → AlgebraicComplex) (φ : K →+* AlgebraicComplex)
    (n : ℕ) (hr : 0<n+1) (c : Fin (n+1) → RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (E : ℝ) (hsource : SelectedFuchsSourceData G a φ (n+1) hr c T UI E) :
    let t := T.map (algebraMap (𝓞 K) K)
    let U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K) :=
      fun i j => (UI i j).map (algebraMap (𝓞 K) K)
    PowerSeries.constantCoeff K (sameCompanionEulerDenominatorSeries t) ≠ 0 ∧
    (∀ j,(t:PowerSeries K)*sameCompanionEulerLastRowSeries n t U j=
      (PowerSeries.X:PowerSeries K)^(n+1-j.val)*(U (Fin.last n) j:PowerSeries K)) ∧
    (sameCompanionEulerPowerSeriesMatrix n t U).map (PowerSeries.constantCoeff K)=
      regularCompanionResidue n (t.coeff t.natTrailingDegree) (polynomialCompanionFace n 1 1 t U) := by
  obtain ⟨hdata,hT,hclear,htop,hqn,hann,hmin,hE,hden,hrest⟩ := hsource
  have hV := companion_common_denominators_local_bounds n c _ _ hT hclear E hE hden
  exact (sameClearing_regularEulerPowerSeries_coefficients n c _ _ hT hclear hV).2

end StrictEUnit
end
