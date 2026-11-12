import FrobeniusIntegerShiftEquation

/-!
# Every integral resonance class of the exact retained Fourier family

Class membership supplies its integer Laurent shift; no rationality premise or
external shift data are required. The base exponent remains external, but all
members of its class are represented in the SAME Laurent-log ring and satisfy
one common literal twisted equation there. No combination of different classes
or full solution-space spanning theorem is claimed.
-/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K]

/-- Indices whose external exponent differs from the base by an integer. -/
def frobeniusResonanceIndex {ν : ℕ} (rho : Fin ν → K) (ξ : K) :=
  {j : Fin ν // ∃ s : ℤ,rho j = ξ + (s : K)}

instance frobeniusResonanceIndexFintype {ν : ℕ} (rho : Fin ν → K) (ξ : K) :
    Fintype (frobeniusResonanceIndex rho ξ) := by
  unfold frobeniusResonanceIndex
  infer_instance

/-- The shift is derived from class membership, not supplied to the packet. -/
def frobeniusResonanceShift {ν : ℕ} (rho : Fin ν → K) (ξ : K)
    (j : frobeniusResonanceIndex rho ξ) : ℤ := Classical.choose j.2

theorem frobeniusResonanceShift_spec {ν : ℕ} (rho : Fin ν → K) (ξ : K)
    (j : frobeniusResonanceIndex rho ξ) :
    rho j.1 = ξ + (frobeniusResonanceShift rho ξ j : K) := Classical.choose_spec j.2

variable [CharZero K]

/-- Independence and the common literal equation for EVERY integral class of
the exact hf/e/rho/p family. Class membership derives all integer shifts. -/
theorem sameFourierTwistedAmplitude_indexed_resonance_solutions
    {μ ν : ℕ} (A : Fin (μ+1) → Fin (ν+1) → K)
    (hf : Stage56FiniteFuchs A) (hc : A (Fin.last μ) (Fin.last ν) ≠ 0)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin ν)
    (rho : Fin ν → K) (p : Fin ν → Polynomial (LaurentSeries K))
    (hrho : ∀ j,rho j = frobeniusRootSeedExponent _ (e.symm j))
    (hp : ∀ j,p j = sameFourierTwistedAmplitude A hf (e.symm j)) (ξ : K) :
    LinearIndependent K (fun j : frobeniusResonanceIndex rho ξ =>
      frobeniusIntegerShift (frobeniusResonanceShift rho ξ j) (p j.1)) ∧
    ∀ j : frobeniusResonanceIndex rho ξ,
      scalarTwistedLogOperator ν (fun k => (stage61_fourierLift A hf).coeff k.val) ξ
        (frobeniusIntegerShift (frobeniusResonanceShift rho ξ j) (p j.1)) = 0 := by
  have hshift (j : frobeniusResonanceIndex rho ξ) :
      frobeniusRootSeedExponent _ (e.symm j.1) =
        ξ + (frobeniusResonanceShift rho ξ j : K) :=
    (hrho j.1).symm.trans (frobeniusResonanceShift_spec rho ξ j)
  constructor
  · simp_rw [hp]
    exact sameFourierTwistedAmplitude_resonance_linearIndependent A hf
      (fun j : frobeniusResonanceIndex rho ξ => e.symm j.1)
      (e.symm.injective.comp Subtype.val_injective) ξ
      (frobeniusResonanceShift rho ξ) hshift
  · intro j
    rw [hp]
    exact sameFourierTwistedAmplitude_resonance_equation A hf hc (e.symm j.1)
      ξ (frobeniusResonanceShift rho ξ j) (hshift j)

/-- Universal over the SAME indexed amplitudes; no replacement family,
rational spectrum, ramification or shifted coefficients are supplied. -/
def FourierExactResonanceSolutionData {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) : Prop :=
  ∀ hf : Stage56FiniteFuchs A,
  ∀ e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin ν,
  ∀ rho : Fin ν → K, ∀ p : Fin ν → Polynomial (LaurentSeries K),
    (∀ j,rho j = frobeniusRootSeedExponent _ (e.symm j)) →
    (∀ j,p j = sameFourierTwistedAmplitude A hf (e.symm j)) →
    ∀ ξ : K,
      LinearIndependent K (fun j : frobeniusResonanceIndex rho ξ =>
        frobeniusIntegerShift (frobeniusResonanceShift rho ξ j) (p j.1)) ∧
      ∀ j : frobeniusResonanceIndex rho ξ,
        scalarTwistedLogOperator ν (fun k => (stage61_fourierLift A hf).coeff k.val) ξ
          (frobeniusIntegerShift (frobeniusResonanceShift rho ξ j) (p j.1)) = 0

theorem fourierExactResonanceSolutionData {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (hc : A (Fin.last μ) (Fin.last ν) ≠ 0) :
    FourierExactResonanceSolutionData A := by
  intro hf e rho p hrho hp ξ
  exact sameFourierTwistedAmplitude_indexed_resonance_solutions A hf hc e rho p hrho hp ξ

end StrictEUnit
end

#print axioms StrictEUnit.frobeniusResonanceShift_spec
#print axioms StrictEUnit.sameFourierTwistedAmplitude_indexed_resonance_solutions
#print axioms StrictEUnit.fourierExactResonanceSolutionData
