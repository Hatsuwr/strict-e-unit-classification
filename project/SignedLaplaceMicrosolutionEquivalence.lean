import SignedInverseLaplaceKernelConverse
import SignedLaplaceFourierAttachment

/-!
# Exact Fourier equation iff a polynomial source error

The independent kernel converse constructs the error polynomial. The same
source array and exact Fourier tuple are retained. This optional attachment
uses the signed Fourier provider, whose acceptance is tracked separately;
none of these results selects an operator or an arithmetic solution family.
-/
noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Exact same-array formal micro-solution equivalence. -/
theorem signedLaplace_fourier_zero_iff_source_polynomial {μ ν : ℕ}
    (A : Fin (μ + 1) → Fin (ν + 1) → K) (y : LaurentSeries K) :
    ((∑ l, (stage53_fourierCoeff A l : PowerSeries K) *
      (PowerSeries.derivative K)^[l.val] (signedInverseLaplace y)) = 0) ↔
      ∃ P : Polynomial K, signedLaplaceSourceAction A y = signedLaplacePolynomialInZ P := by
  rw [← signedLaplace_sourceAction A y]
  exact signedInverseLaplace_eq_zero_iff_exists_polynomialInZ _

/-- The literal signed ordinary input is a source micro-solution exactly when
the ORIGINAL factorial series satisfies the SAME Stage53 Fourier equation. -/
theorem signedLaplace_stage41_fourier_zero_iff_source_polynomial {μ ν : ℕ}
    (A : Fin (μ + 1) → Fin (ν + 1) → AlgebraicComplex)
    (a : ℕ → AlgebraicComplex) :
    ((∑ l, (stage53_fourierCoeff A l : PowerSeries AlgebraicComplex) *
      (PowerSeries.derivative AlgebraicComplex)^[l.val] (stage41_strictFormalSeries a)) = 0) ↔
      ∃ P : Polynomial AlgebraicComplex, signedLaplaceSourceAction A
        (HahnSeries.single (1 : ℤ) (1 : AlgebraicComplex) *
          HahnSeries.ofPowerSeries ℤ AlgebraicComplex
            (PowerSeries.mk (fun n => (-1 : AlgebraicComplex) ^ n * a n))) =
          signedLaplacePolynomialInZ P := by
  have h := signedLaplace_fourier_zero_iff_source_polynomial A
    (HahnSeries.single (1 : ℤ) (1 : AlgebraicComplex) *
      HahnSeries.ofPowerSeries ℤ AlgebraicComplex
        (PowerSeries.mk (fun n => (-1 : AlgebraicComplex) ^ n * a n)))
  rw [signedInverseLaplace_stage41] at h
  exact h

end StrictEUnit
end
