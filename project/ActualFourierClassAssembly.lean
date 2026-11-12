import DisjointNaturalResonanceIndex
import AnalyticResonanceSquareBlock

noncomputable section
open scoped Classical
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Disjoint exhaustive blocks of the exact retained Fourier family, with its
original rank and literal amplitude shifts. -/
theorem actualFourier_disjoint_class_assembly {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last μ) (Fin.last ν) ≠ 0)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin ν)
    (rho : Fin ν → K) (p : Fin ν → Polynomial (LaurentSeries K))
    (hrho : ∀ j, rho j = frobeniusRootSeedExponent _ (e.symm j))
    (hp : ∀ j, p j = sameFourierTwistedAmplitude A hf (e.symm j)) :
    ∃ xi : ExponentClass rho → K,
      (∀ c d, c ≠ d → ∀ z : ℤ, xi c - xi d ≠ (z : K)) ∧
      ∃ E : (Σ c, polynomialLogResonanceCoordinateIndex (xi c)
        (sameFourierEulerCoefficientSymbols A hf 0)) ≃ Fin ν,
      (∀ i, rho (E i) = xi i.1 + (i.2.1.1 : K)) ∧
      (∀ i, naturalResonanceFrobeniusAmplitude (sameFourierEulerCoefficientSymbols A hf)
        (xi i.1) i.2 = frobeniusIntegerShift (i.2.1.1 : ℤ) (p (E i))) ∧
      Nat.card (Σ c, polynomialLogResonanceCoordinateIndex (xi c)
        (sameFourierEulerCoefficientSymbols A hf 0)) = ν := by
  obtain ⟨xi, s, hs, hsep, E, hE, hcard⟩ := exists_disjoint_natural_resonance_equiv
    _ (sameFourierEulerIndicial_ne_zero A hf hc) e rho hrho
  refine ⟨xi, hsep, E, ?_, ?_, hcard⟩
  · intro i
    rw [hE, hrho, Equiv.symm_apply_apply]
    rfl
  · intro i
    rw [hE, hp, Equiv.symm_apply_apply]
    rfl

end StrictEUnit
end
