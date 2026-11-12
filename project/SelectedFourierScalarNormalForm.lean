import ActualFourierScalarNormalForm
import SelectedFourierRetainedArithmetic
noncomputable section
open scoped NumberField Matrix
namespace StrictEUnit

theorem actualFourier_scalarNormalForm_of_arithmetic {mu nu : ℕ}
    (A : Fin (mu+1) → Fin (nu+1) → AlgebraicComplex)
    (ha : FourierRetainedArithmeticData A) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last mu) (Fin.last nu) ≠ 0)
    (hroot : ∀ x, (sameFourierEulerCoefficientSymbols A hf 0).eval x = 0 →
      BinomialPrefixDenominators x) :
    Nonempty (Stage33ScalarNormalForm (algebraicClosure ℚ ℂ).toSubfield nu
      (stage53_fourierCoeff A)) := by
  classical
  letI : IsAlgClosed AlgebraicComplex := IsAlgClosure.isAlgClosed ℚ
  let e := Fintype.equivFinOfCardEq (sameFourierTwistedAmplitude_index_card A hf hc)
  exact actualFourier_scalarNormalForm A ha hf hc e
    (fun j => frobeniusRootSeedExponent _ (e.symm j))
    (fun j => sameFourierTwistedAmplitude A hf (e.symm j))
    (fun _ => rfl) (fun _ => rfl) hroot

def SameClearingFourierScalarNormalFormData
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
  Nonempty (Stage33ScalarNormalForm (algebraicClosure ℚ ℂ).toSubfield nu
    (stage53_fourierCoeff A))

theorem selectedFuchsSourceData_fourier_scalarNormalForm
    {K : Type*} [Field K] [NumberField K]
    (G : PowerSeries K) (a : ℕ → AlgebraicComplex) (phi : K →+* AlgebraicComplex)
    (n : ℕ) (hr : 0<n+1) (c : Fin (n+1) → RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (E : ℝ) (hsource : SelectedFuchsSourceData G a phi (n+1) hr c T UI E) :
    SameClearingFourierScalarNormalFormData phi n T UI := by
  have ha := selectedFuchsSourceData_fourier_retained_arithmetic G a phi n hr c T UI E hsource
  have hroot := selectedFuchsSourceData_fourier_indicial_root_arithmetic G a phi n hr c T UI E hsource
  obtain ⟨hdata,hT,hclear,htop,hqn,hann,hmin,hE,hden,hreg,hpTop,hpReg,
    hplusTop,hplusReg,hnuEq,hnuPos,hfinite,hcorner,hrest⟩ := hsource
  exact actualFourier_scalarNormalForm_of_arithmetic _ ha hfinite hcorner (hroot hfinite)
end StrictEUnit
end
