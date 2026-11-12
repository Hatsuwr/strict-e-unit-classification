import ShiftedPolynomialDerivative
import Mathlib.Algebra.Polynomial.Laurent

/-! Actual finite Laurent-mode operator with polynomial logarithmic
coefficients. Leibniz is a separate obligation until explicitly proved. -/
noncomputable section
namespace StrictEUnit
variable {k : Type*} [Field k]

/-- The shifted logarithmic Euler operator, coefficientwise
p_n ↦ p_n' + (n-a)p_n. -/
def laurentLogShift (a : k) :
    LaurentPolynomial (Polynomial k) →ₗ[k] LaurentPolynomial (Polynomial k) where
  toFun f := Finsupp.onFinset f.support
    (fun n => shiftedPolynomialDerivative ((n : k) - a) (f n))
    (by
      intro n hn
      apply Finsupp.mem_support_iff.mpr
      intro hz
      exact hn (by simp only [hz, map_zero]))
  map_add' f g := by
    apply Finsupp.ext
    intro n
    exact map_add (shiftedPolynomialDerivative ((n : k) - a)) (f n) (g n)
  map_smul' c f := by
    apply Finsupp.ext
    intro n
    exact map_smul (shiftedPolynomialDerivative ((n : k) - a)) c (f n)

/-- The unshifted operator. -/
def laurentLogD : LaurentPolynomial (Polynomial k) →ₗ[k] LaurentPolynomial (Polynomial k) :=
  laurentLogShift 0

@[simp] theorem laurentLogShift_coeff (a : k)
    (f : LaurentPolynomial (Polynomial k)) (n : ℤ) :
    laurentLogShift a f n = shiftedPolynomialDerivative ((n : k) - a) (f n) := rfl

@[simp] theorem laurentLogD_coeff (f : LaurentPolynomial (Polynomial k)) (n : ℤ) :
    laurentLogD f n = (f n).derivative + (n : k) • f n := by
  simp [laurentLogD, shiftedPolynomialDerivative_apply]

theorem laurentLogShift_eq (a : k) (f : LaurentPolynomial (Polynomial k)) :
    laurentLogShift a f = laurentLogD f - a • f := by
  apply Finsupp.ext
  intro n
  change (f n).derivative + ((n : k) - a) • f n =
    (f n).derivative + ((n : k) - 0) • f n - a • f n
  rw [sub_zero, sub_smul, add_sub_assoc]

theorem laurentLogShift_iterate_coeff (a : k)
    (f : LaurentPolynomial (Polynomial k)) (n : ℤ) (j : ℕ) :
    (laurentLogShift a)^[j] f n =
      (shiftedPolynomialDerivative ((n : k) - a))^[j] (f n) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', laurentLogShift_coeff, ih,
      Function.iterate_succ_apply']

theorem laurentLogShift_iterate_support_subset (a : k)
    (f : LaurentPolynomial (Polynomial k)) (j : ℕ) :
    ((laurentLogShift a)^[j] f).support ⊆ f.support := by
  intro n hn
  apply Finsupp.mem_support_iff.mpr
  intro hz
  have he := Finsupp.mem_support_iff.mp hn
  rw [laurentLogShift_iterate_coeff, hz, iterate_map_zero] at he
  exact he rfl

theorem laurentLogShift_stable_ideal
    (I : Ideal (LaurentPolynomial (Polynomial k)))
    (hI : ∀ f ∈ I, laurentLogD f ∈ I) (a : k)
    (f : LaurentPolynomial (Polynomial k)) (hf : f ∈ I) (j : ℕ) :
    (laurentLogShift a)^[j] f ∈ I := by
  induction j with
  | zero => exact hf
  | succ j ih =>
    rw [Function.iterate_succ_apply', laurentLogShift_eq]
    apply I.sub_mem (hI _ ih)
    rw [Algebra.smul_def]
    exact I.mul_mem_left _ ih
end StrictEUnit

#print axioms StrictEUnit.laurentLogShift
#print axioms StrictEUnit.laurentLogD
#print axioms StrictEUnit.laurentLogShift_coeff
#print axioms StrictEUnit.laurentLogD_coeff
#print axioms StrictEUnit.laurentLogShift_eq
#print axioms StrictEUnit.laurentLogShift_iterate_coeff
#print axioms StrictEUnit.laurentLogShift_iterate_support_subset
#print axioms StrictEUnit.laurentLogShift_stable_ideal
