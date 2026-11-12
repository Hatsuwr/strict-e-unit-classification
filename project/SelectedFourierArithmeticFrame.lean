import ActualFourierArithmeticFrame

noncomputable section
open scoped NumberField Matrix
namespace StrictEUnit

def SameClearingFourierArithmeticFrameData
    {K : Type*} [Field K] [NumberField K] (phi : K →+* AlgebraicComplex)
    (n : ℕ) (T : Polynomial (𝓞 K))
    (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K))) : Prop :=
  let t := T.map (algebraMap (𝓞 K) K)
  let U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K) :=
    fun i j => (UI i j).map (algebraMap (𝓞 K) K)
  let q := sameCompanionScalarTuple (n+1) (Nat.succ_pos n) t U
  let p : Fin (n+2) → Polynomial AlgebraicComplex := fun i => (q i).map phi
  let qplus := ordinaryReflectionTuple (n+1) p
  let d := reciprocalCommonDegree (n+1) qplus
  let nu := reciprocalSourceDegree (n+1) d qplus
  let A := reciprocalSourceArray (n+1) d qplus
  ∃ F : Stage27ArithmeticFrame (algebraicClosure ℚ ℂ).toSubfield (Fin nu),
    F.B = stage28_laurentCompanion (algebraicClosure ℚ ℂ).toSubfield
      nu (n+1) (stage61_fourierCorner A) (stage53_fourierCoeff A)

theorem selectedFuchsSourceData_fourier_arithmeticFrame
    {K : Type*} [Field K] [NumberField K]
    (G : PowerSeries K) (a : ℕ → AlgebraicComplex) (phi : K →+* AlgebraicComplex)
    (n : ℕ) (hr : 0<n+1) (c : Fin (n+1) → RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (E : ℝ) (hsource : SelectedFuchsSourceData G a phi (n+1) hr c T UI E) :
    SameClearingFourierArithmeticFrameData phi n T UI := by
  have ha := selectedFuchsSourceData_fourier_retained_arithmetic G a phi n hr c T UI E hsource
  have hroot := selectedFuchsSourceData_fourier_indicial_root_arithmetic G a phi n hr c T UI E hsource
  obtain ⟨hdata,hT,hclear,htop,hqn,hann,hmin,hE,hden,hreg,hpTop,hpReg,
    hplusTop,hplusReg,hnuEq,hnuPos,hfinite,hcorner,hrest⟩ := hsource
  exact actualFourier_arithmeticFrame _ ha hfinite hcorner hnuPos (hroot hfinite)
end StrictEUnit
end
