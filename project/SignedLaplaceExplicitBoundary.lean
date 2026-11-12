import SignedLaplaceMicrosolutionEquivalence
import SignedLaplacePolynomialErrorAttachment

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- The boundary polynomial is constructed from the SAME source action,
without supplying a polynomial witness or replacing its coefficient array. -/
def signedLaplaceBoundaryPolynomial {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (y : LaurentSeries K) : Polynomial K :=
  signedLaplaceKernelPolynomial (signedLaplaceSourceAction A y)

theorem signedLaplaceBoundaryPolynomial_coeff {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (y : LaurentSeries K) (k : ℕ) :
    (signedLaplaceBoundaryPolynomial A y).coeff k =
      if k ≤ (-(signedLaplaceSourceAction A y).order).toNat then
        (signedLaplaceSourceAction A y).coeff (-(k:ℤ)) else 0 :=
  signedLaplaceKernelPolynomial_coeff _ k

theorem signedLaplaceBoundaryPolynomial_natDegree_le {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (y : LaurentSeries K) :
    (signedLaplaceBoundaryPolynomial A y).natDegree ≤
      (-(signedLaplaceSourceAction A y).order).toNat :=
  signedLaplaceKernelPolynomial_natDegree_le _

/-- Exact same-array Fourier equation iff the source action equals its
explicit finite boundary polynomial. Source action need not vanish. -/
theorem signedLaplace_fourier_zero_iff_explicit_boundary {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (y : LaurentSeries K) :
    ((∑ l, (stage53_fourierCoeff A l : PowerSeries K) *
      (PowerSeries.derivative K)^[l.val] (signedInverseLaplace y)) = 0) ↔
      signedLaplaceSourceAction A y =
        signedLaplacePolynomialInZ (signedLaplaceBoundaryPolynomial A y) := by
  rw [← signedLaplace_sourceAction A y]
  constructor
  · intro h
    exact signedInverseLaplace_kernel_reconstruct _ h
  · intro h
    rw [h, signedInverseLaplace_polynomialInZ]

/-- Literal original-variable factorial series and its signed ordinary source,
with the boundary polynomial constructed, rather than hypothesized. -/
theorem signedLaplace_factorial_zero_iff_explicit_boundary {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (a : ℕ → K) :
    let y := HahnSeries.single (1:ℤ) (1:K) *
      HahnSeries.ofPowerSeries ℤ K (PowerSeries.mk fun n => (-1:K)^n * a n)
    ((∑ l, (stage53_fourierCoeff A l : PowerSeries K) *
      (PowerSeries.derivative K)^[l.val]
        (PowerSeries.mk fun n => a n/(n.factorial:K))) = 0) ↔
      signedLaplaceSourceAction A y =
        signedLaplacePolynomialInZ (signedLaplaceBoundaryPolynomial A y) := by
  have h := signedLaplace_fourier_zero_iff_explicit_boundary A
    (HahnSeries.single (1:ℤ) (1:K) *
      HahnSeries.ofPowerSeries ℤ K (PowerSeries.mk fun n => (-1:K)^n * a n))
  rw [signedInverseLaplace_signed_input] at h
  exact h

/-- The SAME Stage41 array has this exact boundary contract for the original
factorial series; no source-family existence is asserted. -/
theorem signedLaplace_stage41_zero_iff_explicit_boundary {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → AlgebraicComplex) (a : ℕ → AlgebraicComplex) :
    let y := HahnSeries.single (1:ℤ) (1:AlgebraicComplex) *
      HahnSeries.ofPowerSeries ℤ AlgebraicComplex
        (PowerSeries.mk fun n => (-1:AlgebraicComplex)^n * a n)
    ((∑ l, (stage53_fourierCoeff A l : PowerSeries AlgebraicComplex) *
      (PowerSeries.derivative AlgebraicComplex)^[l.val] (stage41_strictFormalSeries a)) = 0) ↔
      signedLaplaceSourceAction A y =
        signedLaplacePolynomialInZ (signedLaplaceBoundaryPolynomial A y) := by
  have h := signedLaplace_fourier_zero_iff_explicit_boundary A
    (HahnSeries.single (1:ℤ) (1:AlgebraicComplex) *
      HahnSeries.ofPowerSeries ℤ AlgebraicComplex
        (PowerSeries.mk fun n => (-1:AlgebraicComplex)^n * a n))
  rw [signedInverseLaplace_stage41] at h
  exact h

end StrictEUnit
end
