import Mathlib.Algebra.Polynomial.Derivative

/-!
# The finite-support differential-simplicity ingredient

For nonzero c, the polynomial operator p ↦ p' + c p is injective. This is
proved by its top coefficient, not by an assumed spectral projection. It
will separate different Laurent modes in an Euler-plus-logarithm operator.
The Laurent-mode representation and full differential-simplicity argument
are not asserted here.
-/
noncomputable section
namespace StrictEUnit
open Polynomial
variable {k : Type*} [Field k]

/-- The derivative shifted by a scalar multiple of the identity. -/
def shiftedPolynomialDerivative (c : k) : Polynomial k →ₗ[k] Polynomial k :=
  Polynomial.derivative + c • LinearMap.id

@[simp] theorem shiftedPolynomialDerivative_apply (c : k) (p : Polynomial k) :
    shiftedPolynomialDerivative c p = p.derivative + c • p := rfl

/-- Its top coefficient is c times the top coefficient of p. -/
theorem shiftedPolynomialDerivative_top_coeff (c : k) (p : Polynomial k) :
    (shiftedPolynomialDerivative c p).coeff p.natDegree = c * p.leadingCoeff := by
  rw [shiftedPolynomialDerivative_apply, coeff_add, coeff_derivative,
    coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _), zero_mul, zero_add,
    coeff_smul, coeff_natDegree, smul_eq_mul]

/-- No nonzero polynomial is killed by a nonzero scalar shift. -/
theorem shiftedPolynomialDerivative_ne_zero (c : k) (hc : c ≠ 0)
    (p : Polynomial k) (hp : p ≠ 0) : shiftedPolynomialDerivative c p ≠ 0 := by
  intro h
  have hz := congrArg (fun q : Polynomial k => q.coeff p.natDegree) h
  dsimp only at hz
  rw [shiftedPolynomialDerivative_top_coeff, coeff_zero] at hz
  exact (mul_ne_zero hc (leadingCoeff_ne_zero.mpr hp)) hz

/-- The shifted derivative is genuinely injective. -/
theorem shiftedPolynomialDerivative_injective (c : k) (hc : c ≠ 0) :
    Function.Injective (shiftedPolynomialDerivative c) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro p hp
  by_contra h
  exact shiftedPolynomialDerivative_ne_zero c hc p h (LinearMap.mem_ker.mp hp)

/-- Any finite iteration of a nonzero scalar shift preserves nonzeroness. -/
theorem shiftedPolynomialDerivative_iterate_ne_zero (c : k) (hc : c ≠ 0)
    (p : Polynomial k) (hp : p ≠ 0) (n : ℕ) :
    (shiftedPolynomialDerivative c)^[n] p ≠ 0 := by
  induction n with
  | zero => exact hp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact shiftedPolynomialDerivative_ne_zero c hc _ ih

end StrictEUnit
#print axioms StrictEUnit.shiftedPolynomialDerivative
#print axioms StrictEUnit.shiftedPolynomialDerivative_apply
#print axioms StrictEUnit.shiftedPolynomialDerivative_top_coeff
#print axioms StrictEUnit.shiftedPolynomialDerivative_ne_zero
#print axioms StrictEUnit.shiftedPolynomialDerivative_injective
#print axioms StrictEUnit.shiftedPolynomialDerivative_iterate_ne_zero
