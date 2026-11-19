import RationalDerivationExtension
import DerivationOverConstants
import Mathlib.Algebra.Polynomial.Derivation

/-! The actual ordinary derivative on the rational-function field, constructed
from the proved quotient-rule extension rather than postulated. -/
noncomputable section
namespace StrictEUnit
variable {k : Type*} [Field k]

/-- Extend the actual polynomial derivative to rational functions, initially
with its integer-linear structure. -/
def stage14_rationalOrdinaryIntDerivation : Derivation ℤ (RatFunc k) (RatFunc k) :=
  rationalDerivationExtension
    ((Polynomial.derivative' : Derivation k (Polynomial k) (Polynomial k)).restrictScalars ℤ)

/-- The extension agrees with ordinary differentiation on every polynomial. -/
theorem stage14_rationalOrdinaryIntDerivation_polynomial (p : Polynomial k) :
    stage14_rationalOrdinaryIntDerivation (algebraMap (Polynomial k) (RatFunc k) p) =
      algebraMap (Polynomial k) (RatFunc k) p.derivative := by
  exact rationalDerivationExtension_algebraMap _ p

/-- All actual coefficient-field constants have derivative zero. -/
theorem stage14_rationalOrdinaryIntDerivation_constant (c : k) :
    stage14_rationalOrdinaryIntDerivation (algebraMap k (RatFunc k) c) = 0 := by
  rw [IsScalarTower.algebraMap_apply k (Polynomial k) (RatFunc k) c]
  change stage14_rationalOrdinaryIntDerivation
    (algebraMap (Polynomial k) (RatFunc k) (Polynomial.C c)) = 0
  rw [stage14_rationalOrdinaryIntDerivation_polynomial, Polynomial.derivative_C, map_zero]

/-- The ordinary derivation on k(x), linear over its actual coefficient field. -/
def stage14_rationalOrdinaryDerivation : Derivation k (RatFunc k) (RatFunc k) :=
  derivationOverConstants stage14_rationalOrdinaryIntDerivation
    stage14_rationalOrdinaryIntDerivation_constant

/-- Polynomial compatibility for the genuinely k-linear derivation. -/
theorem stage14_rationalOrdinaryDerivation_polynomial (p : Polynomial k) :
    stage14_rationalOrdinaryDerivation (algebraMap (Polynomial k) (RatFunc k) p) =
      algebraMap (Polynomial k) (RatFunc k) p.derivative :=
  stage14_rationalOrdinaryIntDerivation_polynomial p

/-- Compatibility on polynomials forces compatibility on every rational
function, by the proved quotient rule in both fields. -/
theorem stage14_rationalOrdinaryDerivation_compatible
    (D : Derivation k (LaurentSeries k) (LaurentSeries k))
    (hpoly : ∀ p : Polynomial k,
      D (algebraMap (Polynomial k) (LaurentSeries k) p) =
        algebraMap (Polynomial k) (LaurentSeries k) p.derivative)
    (b : RatFunc k) :
    D (algebraMap (RatFunc k) (LaurentSeries k) b) =
      algebraMap (RatFunc k) (LaurentSeries k) (stage14_rationalOrdinaryDerivation b) := by
  induction b using RatFunc.induction_on
  rename_i p q hq
  rw [map_div₀, Derivation.leibniz_div, Derivation.leibniz_div,
    stage14_rationalOrdinaryDerivation_polynomial,
    stage14_rationalOrdinaryDerivation_polynomial]
  simp only [← IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) (LaurentSeries k),
    hpoly, smul_eq_mul, map_sub, map_mul, map_pow, map_div₀, map_inv₀]
end StrictEUnit
