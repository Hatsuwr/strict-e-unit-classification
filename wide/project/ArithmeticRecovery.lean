import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Field.Subfield.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Arithmetic normalization of an already established polynomial phase

This file checks an algebraic step from Section 13 of the proposed strict
E-value-unit argument. It does NOT prove that the analytic logarithm is a
polynomial, that its derivative has algebraic coefficients, or that a
numerical E-unit admits the proposed torsor lift. Those inputs must be
established separately. There are no project axioms or omitted proofs.
-/

namespace StrictEUnit

open Polynomial

/-- In characteristic zero, coefficients of the derivative determine every
nonconstant coefficient over the same subfield. The constant coefficient
must be controlled separately. -/
theorem coefficients_mem_of_derivative
    {K : Type*} [Field K] [CharZero K] (k : Subfield K)
    (P : Polynomial K) (h0 : P.coeff 0 ∈ k)
    (hderiv : ∀ n : ℕ, P.derivative.coeff n ∈ k) :
    ∀ n : ℕ, P.coeff n ∈ k := by
  intro n
  cases n with
  | zero => exact h0
  | succ n =>
      have hn : (n + 1 : K) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero n
      have hquot := k.div_mem (hderiv n) (natCast_mem k (n + 1))
      simpa only [Polynomial.coeff_derivative, Nat.cast_add, Nat.cast_one,
        mul_div_cancel_right₀ _ hn] using hquot

/-- A phase with controlled constant coefficient and derivative actually
comes from a polynomial with coefficients in the chosen subfield. -/
theorem exists_subfield_polynomial_of_derivative
    {K : Type*} [Field K] [CharZero K] (k : Subfield K)
    (P : Polynomial K) (h0 : P.coeff 0 ∈ k)
    (hderiv : ∀ n : ℕ, P.derivative.coeff n ∈ k) :
    ∃ Q : Polynomial k, Q.map k.subtype = P := by
  apply (Polynomial.mem_lifts P).mp
  apply (Polynomial.lifts_iff_coeff_lifts P).mpr
  intro n
  exact ⟨⟨P.coeff n, coefficients_mem_of_derivative k P h0 hderiv n⟩, rfl⟩

/-- Evaluation at any point in the subfield preserves this arithmetic
normalization, in particular at the specialization point `1`. -/
theorem eval_mem_of_derivative
    {K : Type*} [Field K] [CharZero K] (k : Subfield K)
    (P : Polynomial K) (h0 : P.coeff 0 ∈ k)
    (hderiv : ∀ n : ℕ, P.derivative.coeff n ∈ k)
    (x : K) (hx : x ∈ k) : P.eval x ∈ k := by
  obtain ⟨Q, hQ⟩ := exists_subfield_polynomial_of_derivative k P h0 hderiv
  rw [← hQ]
  have heval : (Q.map k.subtype).eval x = ((Q.eval ⟨x, hx⟩ : k) : K) := by
    simpa only [Polynomial.eval_map] using
      (Polynomial.eval₂_at_apply (p := Q) k.subtype ⟨x, hx⟩)
  rw [heval]
  exact (Q.eval ⟨x, hx⟩).property

/-- The normalization `P(0)=0` is sufficient to control the otherwise
undetermined additive constant. -/
theorem eval_one_mem_of_normalized_derivative
    {K : Type*} [Field K] [CharZero K] (k : Subfield K)
    (P : Polynomial K) (h0 : P.coeff 0 = 0)
    (hderiv : ∀ n : ℕ, P.derivative.coeff n ∈ k) : P.eval 1 ∈ k := by
  exact eval_mem_of_derivative k P (by simpa only [h0] using k.zero_mem)
    hderiv 1 k.one_mem

/-- Regression check: derivative coefficients alone do not control the
constant term. An arbitrary constant outside the subfield is a counterexample. -/
theorem constant_term_control_is_necessary
    {K : Type*} [Field K] (k : Subfield K) (c : K) (hc : c ∉ k) :
    (∀ n : ℕ, (Polynomial.C c).derivative.coeff n ∈ k) ∧
      ¬ (∀ n : ℕ, (Polynomial.C c).coeff n ∈ k) := by
  constructor
  · intro n
    simpa only [Polynomial.derivative_C, Polynomial.coeff_zero] using k.zero_mem
  · intro h
    exact hc (by simpa only [Polynomial.coeff_C_zero] using h 0)

/-- A number has the claimed exponential form over a specified subfield.
This is NOT defined to mean an E-value or a unit of an E-value ring. -/
def HasExponentialForm (k : Subfield ℂ) (u : ℂ) : Prop :=
  ∃ a : ℂ, a ∈ k ∧ a ≠ 0 ∧ ∃ b : ℂ, b ∈ k ∧ u = a * Complex.exp b

/-- The proposed class contains `1`, independently of E-function theory. -/
theorem exponential_form_one (k : Subfield ℂ) : HasExponentialForm k 1 := by
  refine ⟨1, k.one_mem, one_ne_zero, 0, k.zero_mem, ?_⟩
  simp

/-- The proposed class is closed under multiplication. -/
theorem exponential_form_mul (k : Subfield ℂ) {u v : ℂ}
    (hu : HasExponentialForm k u) (hv : HasExponentialForm k v) :
    HasExponentialForm k (u * v) := by
  obtain ⟨a, ha, ha0, b, hb, rfl⟩ := hu
  obtain ⟨c, hc, hc0, d, hd, rfl⟩ := hv
  refine ⟨a * c, k.mul_mem ha hc, mul_ne_zero ha0 hc0,
    b + d, k.add_mem hb hd, ?_⟩
  rw [Complex.exp_add]
  ac_rfl

/-- The proposed class is closed under reciprocals. This does not assert that
arbitrary E-values or arbitrary function representatives are closed under them. -/
theorem exponential_form_inv (k : Subfield ℂ) {u : ℂ}
    (hu : HasExponentialForm k u) : HasExponentialForm k u⁻¹ := by
  obtain ⟨a, ha, ha0, b, hb, rfl⟩ := hu
  refine ⟨a⁻¹, k.inv_mem ha, inv_ne_zero ha0, -b, k.neg_mem hb, ?_⟩
  simp only [Complex.exp_neg, mul_inv_rev]
  exact mul_comm _ _

/-- The last scalar multiplication in the manuscript preserves the desired
form once both scalars and the normalized phase have already been justified. -/
theorem exponential_form_of_normalized_phase
    (k : Subfield ℂ) (P : Polynomial ℂ)
    (h0 : P.coeff 0 = 0)
    (hderiv : ∀ n : ℕ, P.derivative.coeff n ∈ k)
    (b c : ℂ) (hb : b ∈ k) (hc : c ∈ k) (hb0 : b ≠ 0) (hc0 : c ≠ 0) :
    HasExponentialForm k (b * (c * Complex.exp (P.eval 1))) := by
  refine ⟨b * c, k.mul_mem hb hc, mul_ne_zero hb0 hc0, P.eval 1,
    eval_one_mem_of_normalized_derivative k P h0 hderiv, ?_⟩
  exact (mul_assoc b c (Complex.exp (P.eval 1))).symm

#print axioms coefficients_mem_of_derivative
#print axioms exists_subfield_polynomial_of_derivative
#print axioms eval_mem_of_derivative
#print axioms eval_one_mem_of_normalized_derivative
#print axioms exponential_form_one
#print axioms exponential_form_mul
#print axioms exponential_form_inv
#print axioms constant_term_control_is_necessary
#print axioms exponential_form_of_normalized_phase

end StrictEUnit
