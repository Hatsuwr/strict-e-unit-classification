import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.Derivation.Basic

noncomputable section
namespace StrictEUnit
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]

/-- Compatibility of a Laurent algebra map with derivations is checked on
just the coordinate and its inverse, since both derivations kill scalars. -/
theorem v5_laurent_derivation_agrees
    (φ : LaurentPolynomial k →ₐ[k] R)
    (d : Derivation k (LaurentPolynomial k) (LaurentPolynomial k))
    (D : Derivation k R R)
    (hpos : D (φ (LaurentPolynomial.T 1)) = φ (d (LaurentPolynomial.T 1)))
    (hneg : D (φ (LaurentPolynomial.T (-1))) = φ (d (LaurentPolynomial.T (-1))))
    (x : LaurentPolynomial k) : D (φ x) = φ (d x) := by
  have hC (a : k) : D (φ (LaurentPolynomial.C a)) = φ (d (LaurentPolynomial.C a)) := by
    change D (φ (algebraMap k (LaurentPolynomial k) a)) =
      φ (d (algebraMap k (LaurentPolynomial k) a))
    rw [φ.commutes, D.map_algebraMap, d.map_algebraMap, map_zero]
  have hmul {x y : LaurentPolynomial k}
      (hx : D (φ x) = φ (d x)) (hy : D (φ y) = φ (d y)) :
      D (φ (x * y)) = φ (d (x * y)) := by
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hx, hy]
  induction x using LaurentPolynomial.induction_on with
  | h_C a => exact hC a
  | h_add hx hy => simp only [map_add, hx, hy]
  | h_C_mul_T n a h =>
    rw [show (n : ℤ) + 1 = (n : ℤ) + (1 : ℤ) from rfl,
      LaurentPolynomial.T_add, ← mul_assoc]
    exact hmul h hpos
  | h_C_mul_T_Z n a h =>
    rw [sub_eq_add_neg, LaurentPolynomial.T_add, ← mul_assoc]
    exact hmul h hneg

end StrictEUnit
#print axioms StrictEUnit.v5_laurent_derivation_agrees
