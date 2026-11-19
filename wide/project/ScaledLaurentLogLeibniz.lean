import ScaledLaurentLogSimplicity
import Mathlib.RingTheory.Derivation.Basic

/-! Leibniz and a bundled derivation for the actual finite Laurent-log
operator. No differential-simplicity assumption is used here. -/
noncomputable section
namespace StrictEUnit
variable {k : Type*} [Field k]
variable (c : k)

@[simp] theorem scaledLaurentLogD_single (n : ℤ) (p : Polynomial k) :
    scaledLaurentLogD c (Finsupp.single n p) =
      Finsupp.single n (p.derivative + (c * (n:k)) • p) := by
  apply Finsupp.ext
  intro j
  by_cases h : n = j
  · subst j
    simp only [scaledLaurentLogD_coeff, Finsupp.single_eq_same]
  · simp only [scaledLaurentLogD_coeff, Finsupp.single_apply, if_neg h,
      Polynomial.derivative_zero, smul_zero, add_zero]

theorem scaledLaurentLogD_mul (f g : LaurentPolynomial (Polynomial k)) :
    scaledLaurentLogD c (f*g) = scaledLaurentLogD c f * g + f * scaledLaurentLogD c g := by
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg => simp only [add_mul, map_add, hf, hg, mul_add]; abel
  | C_mul_T n p =>
    rw [← LaurentPolynomial.single_eq_C_mul_T]
    induction g using LaurentPolynomial.induction_on' with
    | add f g hf hg => simp only [mul_add, map_add, hf, hg, add_mul]; abel
    | C_mul_T m q =>
      rw [← LaurentPolynomial.single_eq_C_mul_T]
      simp only [AddMonoidAlgebra.single_mul_single, scaledLaurentLogD_single]
      rw [← Finsupp.single_add]
      congr 1
      rw [Polynomial.derivative_mul, Int.cast_add, mul_add, add_smul]
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
      abel

/-- The actual logarithmic Euler derivation, as a bundled derivation. -/
def scaledLaurentLogDerivation :
    Derivation k (LaurentPolynomial (Polynomial k)) (LaurentPolynomial (Polynomial k)) :=
  Derivation.mk' (scaledLaurentLogD c (k:=k)) (fun f g => by
    change scaledLaurentLogD c (f*g) = f * scaledLaurentLogD c g + g * scaledLaurentLogD c f
    rw [scaledLaurentLogD_mul]
    ring)

@[simp] theorem scaledLaurentLogDerivation_apply
    (f : LaurentPolynomial (Polynomial k)) :
    scaledLaurentLogDerivation c f = scaledLaurentLogD c f := rfl

#print axioms scaledLaurentLogD_single
#print axioms scaledLaurentLogD_mul
#print axioms scaledLaurentLogDerivation
#print axioms scaledLaurentLogDerivation_apply
end StrictEUnit
