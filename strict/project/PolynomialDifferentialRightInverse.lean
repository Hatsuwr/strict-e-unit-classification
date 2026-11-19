import ShiftedPolynomialDerivative
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.Abel

/-!
# Explicit polynomial right inverses for logarithmic recurrence

The inverse of D+c is a finite recursive expression and does not require
characteristic zero. Integration and the description of ker D^q require it.
These are polynomial-algebra ingredients only: no Frobenius basis, arithmetic
growth, rational exponent, or strict-E condition is asserted here.

SOURCE-ONLY DRAFT until a separate coordinated compiler check succeeds.
-/
noncomputable section
open Polynomial
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K]

/-- The truncated geometric inverse, with the derivative applied recursively. -/
def polynomialShiftInverseAux (c : K) : ℕ → Polynomial K → Polynomial K
  | 0, _ => 0
  | n + 1, p => c⁻¹ • (p - polynomialShiftInverseAux c n p.derivative)

/-- A finite bound on derivative nilpotence suffices for the exact inverse. -/
theorem polynomialShiftInverseAux_rightInverse (c : K) (hc : c ≠ 0)
    (n : ℕ) (p : Polynomial K)
    (hp : (Polynomial.derivative : Polynomial K → Polynomial K)^[n] p = 0) :
    shiftedPolynomialDerivative c (polynomialShiftInverseAux c n p) = p := by
  induction n generalizing p with
  | zero =>
    have hp0 : p = 0 := hp
    subst p
    simp [polynomialShiftInverseAux]
  | succ n ih =>
    have hpd : (Polynomial.derivative : Polynomial K → Polynomial K)^[n]
        p.derivative = 0 := by
      simpa only [Function.iterate_succ_apply] using hp
    have hq := ih p.derivative hpd
    rw [shiftedPolynomialDerivative_apply] at hq
    have hsub : p.derivative -
        (polynomialShiftInverseAux c n p.derivative).derivative =
        c • polynomialShiftInverseAux c n p.derivative := by
      exact sub_eq_iff_eq_add.mpr (hq.symm.trans (add_comm _ _))
    rw [polynomialShiftInverseAux, shiftedPolynomialDerivative_apply,
      Polynomial.derivative_smul, Polynomial.derivative_sub,
      smul_smul, mul_inv_cancel₀ hc, one_smul, hsub,
      smul_smul, inv_mul_cancel₀ hc, one_smul]
    abel

/-- No truncated inverse raises polynomial degree. -/
theorem polynomialShiftInverseAux_natDegree_le (c : K) (n : ℕ)
    (p : Polynomial K) :
    (polynomialShiftInverseAux c n p).natDegree ≤ p.natDegree := by
  induction n generalizing p with
  | zero => simp [polynomialShiftInverseAux]
  | succ n ih =>
    exact (Polynomial.natDegree_smul_le _ _).trans
      ((Polynomial.natDegree_sub_le _ _).trans
        (max_le le_rfl ((ih p.derivative).trans
          ((Polynomial.natDegree_derivative_le p).trans (Nat.sub_le _ _)))))

/-- The full inverse uses the explicit nilpotence bound deg(p)+1. -/
def polynomialShiftInverse (c : K) (p : Polynomial K) : Polynomial K :=
  polynomialShiftInverseAux c (p.natDegree + 1) p

@[simp] theorem polynomialShiftInverse_rightInverse (c : K) (hc : c ≠ 0)
    (p : Polynomial K) :
    shiftedPolynomialDerivative c (polynomialShiftInverse c p) = p :=
  polynomialShiftInverseAux_rightInverse c hc _ p
    (Polynomial.iterate_derivative_eq_zero (Nat.lt_succ_self _))

theorem polynomialShiftInverse_natDegree_le (c : K) (p : Polynomial K) :
    (polynomialShiftInverse c p).natDegree ≤ p.natDegree :=
  polynomialShiftInverseAux_natDegree_le c _ p

/-- The right inverse is also a left inverse, by the existing injectivity proof. -/
@[simp] theorem polynomialShiftInverse_leftInverse (c : K) (hc : c ≠ 0)
    (p : Polynomial K) :
    polynomialShiftInverse c (shiftedPolynomialDerivative c p) = p := by
  apply shiftedPolynomialDerivative_injective c hc
  exact polynomialShiftInverse_rightInverse c hc _

/-- The explicit construction establishes surjectivity rather than assuming it. -/
theorem shiftedPolynomialDerivative_surjective (c : K) (hc : c ≠ 0) :
    Function.Surjective (shiftedPolynomialDerivative c) :=
  fun p => ⟨polynomialShiftInverse c p, polynomialShiftInverse_rightInverse c hc p⟩

/-- The nonzero-shift equation has exactly one polynomial solution. -/
theorem polynomialShiftInverse_unique (c : K) (hc : c ≠ 0)
    (p q : Polynomial K) :
    shiftedPolynomialDerivative c q = p ↔ q = polynomialShiftInverse c p := by
  constructor
  · intro h
    apply shiftedPolynomialDerivative_injective c hc
    rw [h, polynomialShiftInverse_rightInverse c hc]
  · rintro rfl
    exact polynomialShiftInverse_rightInverse c hc p

/-- A repeated nonzero factor is inverted by the repeated explicit inverse. -/
theorem polynomialShiftInverse_iterate_rightInverse (c : K) (hc : c ≠ 0)
    (q : ℕ) (p : Polynomial K) :
    (shiftedPolynomialDerivative c)^[q] ((polynomialShiftInverse c)^[q] p) = p :=
  (Function.RightInverse.iterate (polynomialShiftInverse_rightInverse c hc) q) p

/-- Repeated nonresonant factors still cost no logarithmic degree. -/
theorem polynomialShiftInverse_iterate_natDegree_le (c : K)
    (q : ℕ) (p : Polynomial K) :
    ((polynomialShiftInverse c)^[q] p).natDegree ≤ p.natDegree := by
  induction q with
  | zero => exact le_rfl
  | succ q ih =>
    rw [Function.iterate_succ_apply']
    exact (polynomialShiftInverse_natDegree_le c _).trans ih

/-- The coefficientwise primitive with integration constant fixed to zero. -/
def polynomialPrimitive (p : Polynomial K) : Polynomial K :=
  p.sum fun n a => Polynomial.monomial (n + 1) (a / (n + 1 : K))

@[simp] theorem polynomialPrimitive_coeff_zero (p : Polynomial K) :
    (polynomialPrimitive p).coeff 0 = 0 := by
  classical
  simp [polynomialPrimitive, Polynomial.sum_def, Polynomial.finset_sum_coeff,
    Polynomial.coeff_monomial]

theorem polynomialPrimitive_natDegree_le (p : Polynomial K) :
    (polynomialPrimitive p).natDegree ≤ p.natDegree + 1 := by
  classical
  unfold polynomialPrimitive
  rw [Polynomial.sum_def]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro n hn
  exact (Polynomial.natDegree_monomial_le _).trans
    (Nat.succ_le_succ (Polynomial.le_natDegree_of_mem_supp n hn))

section CharZero
variable [CharZero K]

/-- Literal differentiation cancels the nonzero coefficient denominators. -/
@[simp] theorem polynomialPrimitive_rightInverse (p : Polynomial K) :
    (polynomialPrimitive p).derivative = p := by
  classical
  unfold polynomialPrimitive
  rw [Polynomial.sum_def, Polynomial.derivative_sum]
  calc
    _ = ∑ n ∈ p.support, Polynomial.monomial n (p.coeff n) := by
      apply Finset.sum_congr rfl
      intro n _
      have hn : (n + 1 : K) ≠ 0 := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n) : ((n + 1 : ℕ) : K) ≠ 0)
      rw [Polynomial.derivative_monomial_succ, div_mul_cancel₀ _ hn]
    _ = p := Polynomial.sum_monomial_eq p

/-- The canonical q-fold primitive; q=0 is deliberately included. -/
def polynomialIteratedPrimitive (q : ℕ) (p : Polynomial K) : Polynomial K :=
  polynomialPrimitive^[q] p

/-- Repeated integration is a concrete right inverse for D^q. -/
@[simp] theorem polynomialIteratedPrimitive_rightInverse (q : ℕ) (p : Polynomial K) :
    (Polynomial.derivative : Polynomial K → Polynomial K)^[q]
      (polynomialIteratedPrimitive q p) = p :=
  (Function.RightInverse.iterate polynomialPrimitive_rightInverse q) p

theorem polynomialIteratedPrimitive_natDegree_le (q : ℕ) (p : Polynomial K) :
    (polynomialIteratedPrimitive q p).natDegree ≤ p.natDegree + q := by
  induction q with
  | zero => simp [polynomialIteratedPrimitive]
  | succ q ih =>
    change (polynomialPrimitive^[q + 1] p).natDegree ≤ _
    rw [Function.iterate_succ_apply']
    exact (polynomialPrimitive_natDegree_le _).trans
      (by simpa only [Nat.add_assoc] using Nat.succ_le_succ ih)

/-- The kernel is exactly the polynomials with no coefficient in degree ≥q.
Unlike a natDegree-only statement this also handles q=0 and the zero polynomial. -/
theorem polynomial_iterate_derivative_eq_zero_iff_coeff (q : ℕ) (p : Polynomial K) :
    (Polynomial.derivative : Polynomial K → Polynomial K)^[q] p = 0 ↔
      ∀ n : ℕ, q ≤ n → p.coeff n = 0 := by
  constructor
  · intro hp n hn
    have h := congrArg (fun r : Polynomial K => r.coeff (n - q)) hp
    dsimp only at h
    rw [Polynomial.coeff_iterate_derivative, Nat.sub_add_cancel hn,
      Polynomial.coeff_zero, nsmul_eq_mul] at h
    have hnq : (n.descFactorial q : K) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr
        (fun hz => (Nat.not_lt_of_ge hn) (Nat.descFactorial_eq_zero_iff_lt.mp hz))
    exact (mul_eq_zero.mp h).resolve_left hnq
  · intro hp
    ext n
    rw [Polynomial.coeff_iterate_derivative, hp (n + q) (Nat.le_add_left q n),
      smul_zero, Polynomial.coeff_zero]

/-- Equivalently ker D^q consists precisely of polynomials of degree less than q. -/
theorem polynomial_iterate_derivative_eq_zero_iff_degree (q : ℕ) (p : Polynomial K) :
    (Polynomial.derivative : Polynomial K → Polynomial K)^[q] p = 0 ↔
      p.degree < (q : WithBot ℕ) := by
  rw [polynomial_iterate_derivative_eq_zero_iff_coeff,
    Polynomial.degree_lt_iff_coeff_zero]

/-- Every solution differs from the explicit repeated primitive by a polynomial
of degree less than q. This retains the resonant integration constants. -/
theorem polynomial_iterate_derivative_solution_iff (q : ℕ) (p f : Polynomial K) :
    (Polynomial.derivative : Polynomial K → Polynomial K)^[q] f = p ↔
      ∃ r : Polynomial K, r.degree < (q : WithBot ℕ) ∧
        f = polynomialIteratedPrimitive q p + r := by
  constructor
  · intro hf
    refine ⟨f - polynomialIteratedPrimitive q p, ?_, ?_⟩
    · apply (polynomial_iterate_derivative_eq_zero_iff_degree q _).mp
      rw [Polynomial.iterate_derivative_sub, hf,
        polynomialIteratedPrimitive_rightInverse, sub_self]
    · abel
  · rintro ⟨r, hr, rfl⟩
    have hz := (polynomial_iterate_derivative_eq_zero_iff_degree q r).mpr hr
    rw [iterate_map_add, polynomialIteratedPrimitive_rightInverse, hz, add_zero]

end CharZero
end StrictEUnit
