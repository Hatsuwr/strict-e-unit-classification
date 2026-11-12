import LaurentLogDerivation
import Mathlib.RingTheory.Derivation.Basic

/-! Leibniz and a bundled derivation for the actual finite Laurent-log
operator. No differential-simplicity assumption is used here. -/
noncomputable section
namespace StrictEUnit
variable {k : Type*} [Field k]

@[simp] theorem laurentLogD_single (n : ℤ) (p : Polynomial k) :
    laurentLogD (Finsupp.single n p) =
      Finsupp.single n (p.derivative + (n:k) • p) := by
  apply Finsupp.ext
  intro j
  by_cases h : n = j
  · subst j
    simp only [laurentLogD_coeff, Finsupp.single_eq_same]
  · simp only [laurentLogD_coeff, Finsupp.single_apply, if_neg h,
      Polynomial.derivative_zero, smul_zero, add_zero]

theorem laurentLogD_mul (f g : LaurentPolynomial (Polynomial k)) :
    laurentLogD (f*g) = laurentLogD f * g + f * laurentLogD g := by
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg => simp only [add_mul, map_add, hf, hg, mul_add]; abel
  | C_mul_T n p =>
    rw [← LaurentPolynomial.single_eq_C_mul_T]
    induction g using LaurentPolynomial.induction_on' with
    | add f g hf hg => simp only [mul_add, map_add, hf, hg, add_mul]; abel
    | C_mul_T m q =>
      rw [← LaurentPolynomial.single_eq_C_mul_T]
      simp only [AddMonoidAlgebra.single_mul_single, laurentLogD_single]
      rw [← Finsupp.single_add]
      congr 1
      rw [Polynomial.derivative_mul, Int.cast_add, add_smul]
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
      abel

/-- The actual logarithmic Euler derivation, as a bundled derivation. -/
def laurentLogDerivation :
    Derivation k (LaurentPolynomial (Polynomial k)) (LaurentPolynomial (Polynomial k)) :=
  Derivation.mk' (laurentLogD (k:=k)) (fun f g => by
    change laurentLogD (f*g) = f * laurentLogD g + g * laurentLogD f
    rw [laurentLogD_mul]
    ring)

@[simp] theorem laurentLogDerivation_apply
    (f : LaurentPolynomial (Polynomial k)) :
    laurentLogDerivation f = laurentLogD f := rfl

#print axioms laurentLogD_single
#print axioms laurentLogD_mul
#print axioms laurentLogDerivation
#print axioms laurentLogDerivation_apply
end StrictEUnit
