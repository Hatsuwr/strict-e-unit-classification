import BinomialPrefixRationality
import ResidueEigenvalueBinomialArithmetic

noncomputable section
open scoped Matrix
namespace StrictEUnit

/-- Actual regular-connection residue eigenvalues with nonzero eigenvectors
are rational, from the previously derived matrix arithmetic. -/
theorem regularEulerPrefixArithmetic_eigenvalue_rational
    {K : Type*} [Field K] [NumberField K] {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (hC : RegularEulerPrefixArithmetic C)
    (xi : K) (v : Fin r → K)
    (hv : (C.map (PowerSeries.constantCoeff K))*ᵥv = xi • v)
    (k : Fin r) (hk : v k ≠ 0) : ∃ q : ℚ, algebraMap ℚ K q = xi :=
  binomialPrefixDenominators_rational xi
    (regularEulerPrefixArithmetic_eigenvalue C hC xi v hv k hk)

/-- Rationality for the actual algebraic complex exponents; no finite-field
assumption on the algebraic closure itself. -/
theorem algebraicComplex_binomialPrefixDenominators_rational
    (a : AlgebraicComplex) (ha : BinomialPrefixDenominators a) :
    ∃ q : ℚ, algebraMap ℚ AlgebraicComplex q = a :=
  algebraic_binomialPrefixDenominators_rational a
    (Algebra.IsIntegral.isIntegral a) ha

end StrictEUnit
end
