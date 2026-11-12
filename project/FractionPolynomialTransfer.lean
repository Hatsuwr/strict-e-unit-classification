import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic.Ring

/-!
New proof reconstruction, not recovered historical source.

A polynomial relation on a fraction in a field can be transferred through an
injective homomorphism back to its numerator/denominator ring, and then through
an arbitrary homomorphism to another field.  The proof clears the denominator
in a finite sum before applying injectivity.  It never evaluates a formal
infinite series at a point.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators

namespace StrictEUnit

/-- Homogeneous evaluation of a polynomial, using its original natural degree.
The definition makes sense before either argument is invertible. -/
def fractionClearedEval {R A : Type*} [Semiring R] [CommSemiring A]
    (p : Polynomial R) (c : R →+* A) (a b : A) : A :=
  ∑ i ∈ Finset.range (p.natDegree + 1),
    c (p.coeff i) * a ^ i * b ^ (p.natDegree - i)

/-- Clearing the denominator of polynomial evaluation in a field. -/
theorem eval₂_div_mul_pow_eq_fractionClearedEval
    {R K : Type*} [Semiring R] [Field K]
    (p : Polynomial R) (c : R →+* K) (a b : K) (hb : b ≠ 0) :
    p.eval₂ c (a / b) * b ^ p.natDegree = fractionClearedEval p c a b := by
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_mul]
  unfold fractionClearedEval
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ p.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  calc
    c (p.coeff i) * (a / b) ^ i * b ^ p.natDegree =
        (c (p.coeff i) * a ^ i) * ((b ^ i)⁻¹ * b ^ i) *
          b ^ (p.natDegree - i) := by
      rw [div_pow, div_eq_mul_inv, ← pow_mul_pow_sub b hin]
      ring
    _ = c (p.coeff i) * a ^ i * b ^ (p.natDegree - i) := by
      rw [inv_mul_cancel₀ (pow_ne_zero i hb), mul_one]

/-- Ring homomorphisms commute with the finite, denominator-cleared expression. -/
theorem map_fractionClearedEval
    {R A B : Type*} [Semiring R] [CommSemiring A] [CommSemiring B]
    (p : Polynomial R) (c : R →+* A) (φ : A →+* B) (a b : A) :
    φ (fractionClearedEval p c a b) =
      fractionClearedEval p (φ.comp c) (φ a) (φ b) := by
  simp only [fractionClearedEval, map_sum, map_mul, map_pow, RingHom.comp_apply]

/-- Injectivity transfers the cleared relation into the numerator/denominator
ring.  This is the only step in which the ambient field is used. -/
theorem fractionClearedEval_eq_zero_of_injective
    {R A K : Type*} [Semiring R] [CommSemiring A] [Field K]
    (p : Polynomial R) (c : R →+* A) (φ : A →+* K)
    (hφ : Function.Injective φ) (a b : A) (hb : b ≠ 0)
    (hroot : p.eval₂ (φ.comp c) (φ a / φ b) = 0) :
    fractionClearedEval p c a b = 0 := by
  have hφb : φ b ≠ 0 := by
    intro h
    apply hb
    apply hφ
    simpa only [map_zero] using h
  apply hφ
  rw [map_zero, map_fractionClearedEval,
    ← eval₂_div_mul_pow_eq_fractionClearedEval p (φ.comp c) (φ a) (φ b) hφb,
    hroot, zero_mul]

/-- Once the relation has been transferred into the actual ring, any evaluation
homomorphism may be used, provided its denominator does not vanish. -/
theorem eval₂_div_eq_zero_of_fractionClearedEval_eq_zero
    {R A L : Type*} [Semiring R] [CommSemiring A] [Field L]
    (p : Polynomial R) (c : R →+* A) (ψ : A →+* L)
    (a b : A) (hψb : ψ b ≠ 0)
    (hclear : fractionClearedEval p c a b = 0) :
    p.eval₂ (ψ.comp c) (ψ a / ψ b) = 0 := by
  have hm : p.eval₂ (ψ.comp c) (ψ a / ψ b) * (ψ b) ^ p.natDegree = 0 := by
    rw [eval₂_div_mul_pow_eq_fractionClearedEval p (ψ.comp c) (ψ a) (ψ b) hψb,
      ← map_fractionClearedEval, hclear, map_zero]
  exact (mul_eq_zero.mp hm).resolve_right (pow_ne_zero _ hψb)

/-- A polynomial relation on a fraction transfers from one field realization
to another through an injectively realized numerator/denominator ring. -/
theorem eval₂_div_eq_zero_of_injective
    {R A K L : Type*} [Semiring R] [CommSemiring A] [Field K] [Field L]
    (p : Polynomial R) (c : R →+* A) (φ : A →+* K)
    (hφ : Function.Injective φ) (ψ : A →+* L)
    (a b : A) (hb : b ≠ 0) (hψb : ψ b ≠ 0)
    (hroot : p.eval₂ (φ.comp c) (φ a / φ b) = 0) :
    p.eval₂ (ψ.comp c) (ψ a / ψ b) = 0 :=
  eval₂_div_eq_zero_of_fractionClearedEval_eq_zero p c ψ a b hψb
    (fractionClearedEval_eq_zero_of_injective p c φ hφ a b hb hroot)

end StrictEUnit
