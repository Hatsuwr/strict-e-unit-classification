import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

/-!
# Rational spectrum under scalar residue shifts

An explicit translated annihilating polynomial transfers roots of the shifted
matrix's minimal polynomial to roots of the original one. The target algebra
is the actual, generally noncommutative matrix algebra. No commutative-target
minimal-polynomial translation theorem or spectral conclusion is assumed.
-/
noncomputable section
namespace StrictEUnit
variable {k n : Type*} [Field k] [Fintype n] [DecidableEq n]

/-- Translating the variable back by the scalar gives an annihilating
polynomial for the shifted matrix, in its noncommutative matrix algebra. -/
theorem stage31_scalarShift_aeval_minpoly_comp
    (M : Matrix n n k) (s : k) :
    Polynomial.aeval (M - s • (1 : Matrix n n k))
      ((minpoly k M).comp (Polynomial.X + Polynomial.C s)) = 0 := by
  rw [Polynomial.aeval_comp, Polynomial.aeval_add, Polynomial.aeval_X,
    Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, sub_add_cancel]
  exact minpoly.aeval k M

/-- Every root of the shifted minimal polynomial translates to an actual
root of the original minimal polynomial. -/
theorem stage31_scalarShift_minpoly_root
    (M : Matrix n n k) (s a : k)
    (ha : (minpoly k (M - s • (1 : Matrix n n k))).IsRoot a) :
    (minpoly k M).IsRoot (a + s) := by
  have h := ha.dvd (minpoly.dvd k (M - s • (1 : Matrix n n k))
    (stage31_scalarShift_aeval_minpoly_comp M s))
  simpa only [Polynomial.IsRoot, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C] using h

/-- Subtraction of a rational scalar residue preserves rational
minimal-polynomial roots, with the translated witness explicitly subtracted. -/
theorem stage31_rationalShift_rational_spectrum [CharZero k]
    (M : Matrix n n k) (s : ℚ)
    (hrat : ∀ a : k, (minpoly k M).IsRoot a → ∃ q : ℚ, (q : k) = a) :
    ∀ a : k, (minpoly k (M - (s : k) • (1 : Matrix n n k))).IsRoot a →
      ∃ q : ℚ, (q : k) = a := by
  intro a ha
  obtain ⟨q, hq⟩ := hrat (a + (s : k))
    (stage31_scalarShift_minpoly_root M (s : k) a ha)
  refine ⟨q - s, ?_⟩
  rw [Rat.cast_sub, hq, add_sub_cancel_right]

/-- Integer pole-clearing shifts are a special case of the rational shift. -/
theorem stage31_integerShift_rational_spectrum [CharZero k]
    (M : Matrix n n k) (s : ℤ)
    (hrat : ∀ a : k, (minpoly k M).IsRoot a → ∃ q : ℚ, (q : k) = a) :
    ∀ a : k, (minpoly k (M - (s : k) • (1 : Matrix n n k))).IsRoot a →
      ∃ q : ℚ, (q : k) = a := by
  simpa only [Rat.cast_intCast] using stage31_rationalShift_rational_spectrum M (s : ℚ) hrat

/-- Natural pole-clearing shifts are a special case of the rational shift. -/
theorem stage31_natShift_rational_spectrum [CharZero k]
    (M : Matrix n n k) (s : ℕ)
    (hrat : ∀ a : k, (minpoly k M).IsRoot a → ∃ q : ℚ, (q : k) = a) :
    ∀ a : k, (minpoly k (M - (s : k) • (1 : Matrix n n k))).IsRoot a →
      ∃ q : ℚ, (q : k) = a := by
  simpa only [Rat.cast_natCast] using stage31_rationalShift_rational_spectrum M (s : ℚ) hrat

end StrictEUnit
