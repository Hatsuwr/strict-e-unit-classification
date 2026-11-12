import FourierRetainedArithmeticPacket
import SelectedFourierUniformConjugates
import SelectedFuchsSourceData

noncomputable section
open scoped BigOperators Matrix NumberField
namespace StrictEUnit

/-- A single conjugate-growth constant for the SAME selected Fourier family,
with shared exponential prefix denominators. -/
def SameClearingFourierRetainedDenominatorData
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
  FourierRetainedDenominatorData A

theorem selectedFuchsSourceData_fourier_retained_denominators
    {K : Type*} [Field K] [NumberField K]
    (G : PowerSeries K) (a : ℕ → AlgebraicComplex) (φ : K →+* AlgebraicComplex)
    (n : ℕ) (hr : 0<n+1) (c : Fin (n+1) → RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (E : ℝ) (hsource : SelectedFuchsSourceData G a φ (n+1) hr c T UI E) :
    SameClearingFourierRetainedDenominatorData φ n T UI := by
  have hsourceFull := hsource
  obtain ⟨hdata,hT,hclear,htop,hqn,hann,hmin,hE,hden,hreg,hpTop,hpReg,
    hplusTop,hplusReg,hνeq,hνpos,hfinite,hcorner,hrest⟩ := hsource
  intro hf e rho p hrho hp
  obtain ⟨C,hC,hden⟩ := selectedFuchsSourceData_retained_amplitude_denominators
    G a φ n hr c T UI E hsourceFull _ rfl hf hcorner e rho p hrho hp
  refine ⟨C,hC,fun N =>?_⟩
  obtain ⟨D,hD,hDb,hDi⟩ := hden N
  exact ⟨D,hD,hDb,fun i m hm t =>by
    simpa only [logAmplitudeFactorialCoefficient,mul_assoc] using hDi i m hm t⟩

end StrictEUnit
end

#print axioms StrictEUnit.selectedFuchsSourceData_fourier_retained_denominators
