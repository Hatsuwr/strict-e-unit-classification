import FrobeniusFactorialDenominatorStep

/-! The arithmetic step is transported to the SAME retained amplitude family.
No assertion about cumulative exponential denominator growth is introduced. -/
noncomputable section
open scoped NumberField BigOperators Classical
namespace StrictEUnit

theorem sameFourier_normalized_integer_denominator_steps
    {μ ν : ℕ} (A : Fin (μ+1) → Fin (ν+1) → AlgebraicComplex)
    (hf : Stage56FiniteFuchs A) (hc : A (Fin.last μ) (Fin.last ν)≠0)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin ν)
    (rho : Fin ν → AlgebraicComplex) (p : Fin ν → Polynomial (LaurentSeries AlgebraicComplex))
    (hrho : ∀ i,rho i=frobeniusRootSeedExponent _ (e.symm i))
    (hp : ∀ i,p i=sameFourierTwistedAmplitude A hf (e.symm i))
    (F : IntermediateField ℚ AlgebraicComplex) (hF : FiniteDimensional ℚ F) :
    ∃ E : IntermediateField ℚ AlgebraicComplex,FiniteDimensional ℚ E ∧ F≤E ∧
      (∀ i,rho i∈E) ∧ (∀ k j,(sameFourierEulerCoefficientSymbols A hf k).coeff j∈E) ∧
      ∃ b N : ℕ,0<b ∧ 0<N ∧
        (∀ (i : Fin ν) (k s j : ℕ),IsIntegral ℤ ((b : AlgebraicComplex)*
          ((sameFourierEulerCoefficientSymbols A hf k).comp
            (Polynomial.X+Polynomial.C (rho i+(s : AlgebraicComplex)))).coeff j)) ∧
        ∀ (i : Fin ν) (n : ℕ),N≤n →
          ∃ v : 𝓞 E,v≠0 ∧ ((v : E) : AlgebraicComplex)=
            (b : AlgebraicComplex)*(sameFourierEulerCoefficientSymbols A hf 0).eval (rho i+(n : AlgebraicComplex)) ∧
          ∃ q : ℕ,0<q ∧ q=(Int.natAbs (Algebra.norm ℤ v))^(frobeniusRootSeedOrder (sameFourierEulerCoefficientSymbols A hf 0) (e.symm i)+ν+1) ∧
            ∀ D : AlgebraicComplex,
              (∀ (s : Fin n) (j : ℕ),IsIntegral ℤ (D*logAmplitudeFactorialCoefficient (p i) j s.val)) →
              ∀ j,IsIntegral ℤ ((q : AlgebraicComplex)*D*logAmplitudeFactorialCoefficient (p i) j n) := by
  obtain ⟨E,hE,hFE,hr,hB,b,N,hb,hN,hclear,hsteps⟩ :=
    sameFourier_retained_integer_denominator_steps A hf hc e rho p hrho hp F hF
  refine ⟨E,hE,hFE,hr,hB,b,N,hb,hN,hclear,?_⟩
  intro i n hn
  obtain ⟨v,hv,hvvalue,q,hq,hqeq,hstep⟩ := hsteps i n hn
  refine ⟨v,hv,hvvalue,q,hq,hqeq,?_⟩
  intro D hprev
  exact integral_denominator_step_factorial_normalization
    (fun s j => ((p i).coeff j).coeff (s : ℤ)) n (hN.trans_le hn) q hstep D hprev

def FourierNormalizedDenominatorStepData {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → AlgebraicComplex) : Prop :=
  ∀ F : IntermediateField ℚ AlgebraicComplex,FiniteDimensional ℚ F →
  ∀ hf : Stage56FiniteFuchs A,
  ∀ e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin ν,
  ∀ rho : Fin ν → AlgebraicComplex,∀ p : Fin ν → Polynomial (LaurentSeries AlgebraicComplex),
    (∀ i,rho i=frobeniusRootSeedExponent _ (e.symm i)) →
    (∀ i,p i=sameFourierTwistedAmplitude A hf (e.symm i)) →
    ∃ E : IntermediateField ℚ AlgebraicComplex,FiniteDimensional ℚ E ∧ F≤E ∧
      (∀ i,rho i∈E) ∧ (∀ k j,(sameFourierEulerCoefficientSymbols A hf k).coeff j∈E) ∧
      ∃ b N : ℕ,0<b ∧ 0<N ∧
        (∀ (i : Fin ν) (k s j : ℕ),IsIntegral ℤ ((b : AlgebraicComplex)*
          ((sameFourierEulerCoefficientSymbols A hf k).comp
            (Polynomial.X+Polynomial.C (rho i+(s : AlgebraicComplex)))).coeff j)) ∧
        ∀ (i : Fin ν) (n : ℕ),N≤n →
          ∃ v : 𝓞 E,v≠0 ∧ ((v : E) : AlgebraicComplex)=
            (b : AlgebraicComplex)*(sameFourierEulerCoefficientSymbols A hf 0).eval (rho i+(n : AlgebraicComplex)) ∧
          ∃ q : ℕ,0<q ∧ q=(Int.natAbs (Algebra.norm ℤ v))^(frobeniusRootSeedOrder (sameFourierEulerCoefficientSymbols A hf 0) (e.symm i)+ν+1) ∧
            ∀ D : AlgebraicComplex,
              (∀ (s : Fin n) (j : ℕ),IsIntegral ℤ (D*logAmplitudeFactorialCoefficient (p i) j s.val)) →
              ∀ j,IsIntegral ℤ ((q : AlgebraicComplex)*D*logAmplitudeFactorialCoefficient (p i) j n)

theorem fourierNormalizedDenominatorStepData {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → AlgebraicComplex)
    (hc : A (Fin.last μ) (Fin.last ν)≠0) : FourierNormalizedDenominatorStepData A := by
  intro F hF hf e rho p hrho hp
  exact sameFourier_normalized_integer_denominator_steps A hf hc e rho p hrho hp F hF

end StrictEUnit
end
