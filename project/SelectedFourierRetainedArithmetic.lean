import FourierRetainedArithmeticPacket
import SelectedFourierUniformConjugates
import SelectedFourierRetainedDenominators
import SelectedFuchsSourceData

noncomputable section
open scoped BigOperators Matrix NumberField
namespace StrictEUnit

def SameClearingFourierRetainedArithmeticData
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
  FourierRetainedArithmeticData A

theorem selectedFuchsSourceData_fourier_retained_arithmetic
    {K : Type*} [Field K] [NumberField K]
    (G : PowerSeries K) (a : ℕ → AlgebraicComplex) (phi : K →+* AlgebraicComplex)
    (n : ℕ) (hr : 0<n+1) (c : Fin (n+1) → RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (E : ℝ) (hsource : SelectedFuchsSourceData G a phi (n+1) hr c T UI E) :
    SameClearingFourierRetainedArithmeticData phi n T UI := by
  exact fourierRetainedArithmeticData_of_growth_denominators _
    (selectedFuchsSourceData_fourier_uniform_conjugates G a phi n hr c T UI E hsource)
    (selectedFuchsSourceData_fourier_retained_denominators G a phi n hr c T UI E hsource)
end StrictEUnit
end
