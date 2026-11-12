import FrobeniusNaturalResonanceBasis
import FourierFiniteTwistedAmplitudes

noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- The natural-resonance coordinate is an exact multiplicity seed of P. -/
def naturalResonanceRootSeed (P : Polynomial K) (ξ : K) (hP : P ≠ 0)
    (i : polynomialLogResonanceCoordinateIndex ξ P) : frobeniusRootSeedIndex P :=
  ⟨⟨ξ + (i.1.1 : K),Multiset.mem_toFinset.mpr
    ((Polynomial.mem_roots hP).mpr
      ((polynomialResonanceIndices_mem_iff_eval_zero ξ P hP i.1.1).mp i.1.2))⟩,i.2⟩

/-- Every new basis amplitude is literally an integer shift of one of the
EXACT retained hf/e/rho/p amplitudes. No replacement family is selected. -/
theorem naturalResonanceFrobeniusAmplitude_retained_fourier_index
    {μ ν : ℕ} (A : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last μ) (Fin.last ν) ≠ 0)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin ν)
    (rho : Fin ν → K) (p : Fin ν → Polynomial (LaurentSeries K))
    (hrho : ∀ j,rho j = frobeniusRootSeedExponent _ (e.symm j))
    (hp : ∀ j,p j = sameFourierTwistedAmplitude A hf (e.symm j))
    (ξ : K) (i : polynomialLogResonanceCoordinateIndex ξ
      (sameFourierEulerCoefficientSymbols A hf 0)) :
    ∃ j : Fin ν,rho j = ξ + (i.1.1 : K) ∧
      naturalResonanceFrobeniusAmplitude (sameFourierEulerCoefficientSymbols A hf) ξ i =
        frobeniusIntegerShift (i.1.1 : ℤ) (p j) := by
  let si := naturalResonanceRootSeed (sameFourierEulerCoefficientSymbols A hf 0) ξ
    (sameFourierEulerIndicial_ne_zero A hf hc) i
  refine ⟨e si,?_,?_⟩
  · rw [hrho,Equiv.symm_apply_apply]
    rfl
  · rw [hp,Equiv.symm_apply_apply]
    rfl

/-- Full basis/unique expansion for ALL nonnegative-power coefficient
solutions of the SAME operator, with explicit links to the retained family. -/
def FourierNaturalBasisData {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) : Prop :=
  ∀ hf : Stage56FiniteFuchs A,∀ ξ : K,
  let B := sameFourierEulerCoefficientSymbols A hf
  Module.finrank K (polynomialLogFormalSolutionSpace B ξ) = polynomialResonanceTotalCost ξ (B 0) ∧
  LinearIndependent K (naturalResonanceFrobeniusCoefficients B ξ) ∧
  (∀ i m,polynomialLogEulerCoefficient B ξ (naturalResonanceFrobeniusCoefficients B ξ i) m = 0) ∧
  (∀ u : ℕ → Polynomial K,(∀ m,polynomialLogEulerCoefficient B ξ u m = 0) →
    ∃! c : polynomialLogResonanceCoordinateIndex ξ (B 0) → K,
      u = ∑ i,c i • naturalResonanceFrobeniusCoefficients B ξ i) ∧
  ∀ e : frobeniusRootSeedIndex (B 0) ≃ Fin ν,
  ∀ rho : Fin ν → K,∀ p : Fin ν → Polynomial (LaurentSeries K),
    (∀ j,rho j = frobeniusRootSeedExponent _ (e.symm j)) →
    (∀ j,p j = sameFourierTwistedAmplitude A hf (e.symm j)) →
    ∀ i : polynomialLogResonanceCoordinateIndex ξ (B 0),
      ∃ j : Fin ν,rho j = ξ + (i.1.1 : K) ∧
        naturalResonanceFrobeniusAmplitude B ξ i = frobeniusIntegerShift (i.1.1 : ℤ) (p j)

theorem fourierNaturalBasisData {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (hc : A (Fin.last μ) (Fin.last ν) ≠ 0) :
    FourierNaturalBasisData A := by
  intro hf ξ
  have hP := sameFourierEulerIndicial_ne_zero A hf hc
  refine ⟨polynomialLogFormalSolutionSpace_finrank_eq_resonanceCost ν
      (fun k => (stage61_fourierLift A hf).coeff k.val) ξ hP,
    naturalResonanceFrobeniusCoefficients_linearIndependent _ ξ,
    naturalResonanceFrobeniusCoefficients_solution ν
      (fun k => (stage61_fourierLift A hf).coeff k.val) ξ hP,
    ?_,?_⟩
  · intro u hu
    exact polynomialLogFormalSolution_existsUnique_expansion ν
      (fun k => (stage61_fourierLift A hf).coeff k.val) ξ hP u hu
  · intro e rho p hrho hp i
    exact naturalResonanceFrobeniusAmplitude_retained_fourier_index A hf hc e rho p hrho hp ξ i

end StrictEUnit
end

#print axioms StrictEUnit.naturalResonanceFrobeniusAmplitude_retained_fourier_index
#print axioms StrictEUnit.fourierNaturalBasisData
