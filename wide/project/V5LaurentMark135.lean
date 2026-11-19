import Mathlib.Algebra.Polynomial.Laurent
noncomputable section
namespace StrictEUnit
def v5LaurentMark135 (k : Type*) [Field k] : LaurentPolynomial k →ₐ[k] k :=
  { LaurentPolynomial.eval₂ (RingHom.id k) (1 : kˣ) with
    commutes' := by intro a; exact LaurentPolynomial.eval₂_C _ _ _ }
theorem v5LaurentMark_map135 {k C : Type*} [Field k] [CommRing C]
    (f : k →+* C) (p : LaurentPolynomial k) :
    f (v5LaurentMark135 k p) = LaurentPolynomial.eval₂ f (1 : Cˣ) p := by
  induction p using LaurentPolynomial.induction_on' with
  | add a b ha hb => simp only [map_add, ha, hb]
  | C_mul_T n a =>
    simp [v5LaurentMark135, LaurentPolynomial.eval₂_C_mul_T]
end StrictEUnit
#print axioms StrictEUnit.v5LaurentMark135
#print axioms StrictEUnit.v5LaurentMark_map135
