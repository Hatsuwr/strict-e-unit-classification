import SignedInverseLaplaceKernel
import SignedLaplaceFourierAttachment

/-!
# Fourier transport modulo polynomial initial-value errors

This NEW source-only attachment depends on the separate new kernel core
and the currently pending signed Fourier attachment. It keeps the same source
array A and the literal Stage53 Fourier tuple. It does not produce a source
equation, an error polynomial, or a full arithmetic micro-solution family.
-/
noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- The exact Fourier equation is equivalent to vanishing of the positive
Laurent coefficients of the SAME source action. -/
theorem signedLaplace_fourier_zero_iff_source_positive_coeff_zero {μ ν : ℕ}
    (A : Fin (μ + 1) → Fin (ν + 1) → K) (y : LaurentSeries K) :
    ((∑ l, (stage53_fourierCoeff A l : PowerSeries K) *
      (PowerSeries.derivative K)^[l.val] (signedInverseLaplace y)) = 0) ↔
      ∀ n : ℕ, (signedLaplaceSourceAction A y).coeff ((n : ℤ) + 1) = 0 := by
  rw [← signedLaplace_sourceAction A y]
  exact signedInverseLaplace_eq_zero_iff _

/-- A polynomial error in z=w⁻¹ suffices; an exactly zero source action is
not required to obtain the original Fourier equation. -/
theorem signedLaplace_same_fourier_of_source_polynomial {μ ν : ℕ}
    (A : Fin (μ + 1) → Fin (ν + 1) → K) (y : LaurentSeries K)
    (P : Polynomial K) (hy : signedLaplaceSourceAction A y = signedLaplacePolynomialInZ P) :
    (∑ l, (stage53_fourierCoeff A l : PowerSeries K) *
      (PowerSeries.derivative K)^[l.val] (signedInverseLaplace y)) = 0 := by
  rw [← signedLaplace_sourceAction A y, hy, signedInverseLaplace_polynomialInZ]

/-- Literal signed ordinary input returns the ORIGINAL factorial series and
the SAME Fourier tuple even when its source action is a polynomial in z. -/
theorem signedLaplace_stage41_same_fourier_of_source_polynomial {μ ν : ℕ}
    (A : Fin (μ + 1) → Fin (ν + 1) → AlgebraicComplex)
    (a : ℕ → AlgebraicComplex) (P : Polynomial AlgebraicComplex)
    (hy : signedLaplaceSourceAction A
      (HahnSeries.single (1 : ℤ) (1 : AlgebraicComplex) *
        HahnSeries.ofPowerSeries ℤ AlgebraicComplex
          (PowerSeries.mk (fun n => (-1 : AlgebraicComplex) ^ n * a n))) =
      signedLaplacePolynomialInZ P) :
    (∑ l, (stage53_fourierCoeff A l : PowerSeries AlgebraicComplex) *
      (PowerSeries.derivative AlgebraicComplex)^[l.val] (stage41_strictFormalSeries a)) = 0 := by
  have h := signedLaplace_same_fourier_of_source_polynomial A _ P hy
  rw [signedInverseLaplace_stage41] at h
  exact h

end StrictEUnit
end
