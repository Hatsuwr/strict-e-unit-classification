import SelectedRetainedAmplitudeDenominators
import FourierUniformConjugateGrowth

noncomputable section
namespace StrictEUnit

def FourierRetainedDenominatorData {mu nu : ℕ}
    (A : Fin (mu+1) →Fin (nu+1) →AlgebraicComplex) : Prop :=
  ∀ hf : Stage56FiniteFuchs A,
  ∀ e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin nu,
  ∀ rho : Fin nu →AlgebraicComplex,∀ p : Fin nu →Polynomial (LaurentSeries AlgebraicComplex),
    (∀ i,rho i=frobeniusRootSeedExponent _ (e.symm i)) →
    (∀ i,p i=sameFourierTwistedAmplitude A hf (e.symm i)) →
    ∃ C : ℝ,1≤C ∧ ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D:ℝ)≤C^(N+1) ∧
      ∀ i m,m≤N →∀ t,IsIntegral ℤ ((D:AlgebraicComplex)*logAmplitudeFactorialCoefficient (p i) t m)

/-- The same literal coefficient family, ONE finite field, and ONE common
geometric constant for both conjugates and shared prefix denominators. -/
def FourierRetainedArithmeticData {mu nu : ℕ}
    (A : Fin (mu+1) →Fin (nu+1) →AlgebraicComplex) : Prop :=
  ∀ F : IntermediateField ℚ AlgebraicComplex,FiniteDimensional ℚ F →
  ∀ hf : Stage56FiniteFuchs A,
  ∀ e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin nu,
  ∀ rho : Fin nu →AlgebraicComplex,∀ p : Fin nu →Polynomial (LaurentSeries AlgebraicComplex),
    (∀ i,rho i=frobeniusRootSeedExponent _ (e.symm i)) →
    (∀ i,p i=sameFourierTwistedAmplitude A hf (e.symm i)) →
    ∃ E : IntermediateField ℚ AlgebraicComplex,FiniteDimensional ℚ E ∧ F≤E ∧
      (∀ i j,A i j∈E) ∧ (∀ i,rho i∈E) ∧
      (∀ i j n,((p i).coeff j).coeff n∈E) ∧
      (∀ i j n,logAmplitudeFactorialCoefficient (p i) j n∈E) ∧
      ∃ C : ℝ,1≤C ∧
        (∀ (sigma : AlgebraicComplex →ₐ[ℚ] ℂ) i j n,
          ‖sigma (logAmplitudeFactorialCoefficient (p i) j n)‖≤C^(n+1)) ∧
        ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D:ℝ)≤C^(N+1) ∧
          ∀ i m,m≤N →∀ t,IsIntegral ℤ ((D:AlgebraicComplex)*logAmplitudeFactorialCoefficient (p i) t m)

theorem fourierRetainedArithmeticData_of_growth_denominators {mu nu : ℕ}
    (A : Fin (mu+1) →Fin (nu+1) →AlgebraicComplex)
    (hg : FourierUniformConjugateGrowthData A) (hd : FourierRetainedDenominatorData A) :
    FourierRetainedArithmeticData A := by
  intro F hF hf e rho p hrho hp
  obtain ⟨E,hE,hFE,hA,hr,hB,hpfield,hfact,C,hC,hraw,hconj⟩ := hg F hF hf e rho p hrho hp
  obtain ⟨B,hB,hden⟩ := hd hf e rho p hrho hp
  refine ⟨E,hE,hFE,hA,hr,hpfield,hfact,max C B,hC.trans (le_max_left _ _),?_,?_⟩
  · intro sigma i j n
    exact (hconj sigma i j n).trans
      (pow_le_pow_left₀ (le_trans zero_le_one hC) (le_max_left _ _) _)
  · intro N
    obtain ⟨D,hD,hDb,hDi⟩ := hden N
    exact ⟨D,hD,hDb.trans (pow_le_pow_left₀ (le_trans zero_le_one hB) (le_max_right _ _) _),hDi⟩
end StrictEUnit
end
