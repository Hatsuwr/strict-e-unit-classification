import StrictETaylorRealization
import Stage14OneSidedArithmeticRecovery
import AlgebraicScalarExponential

/-! Actual strict E-functions with no zeros away from the origin have the
arithmetic determinant shape. This concerns a functional zero set. It does
not turn two inverse numerical representatives into functional inverses. -/
noncomputable section
namespace StrictEUnit

/-- Power-pullback growth follows from the complete strict E definition. -/
theorem strictEFunction_powerExponentialBound {f : ℂ → ℂ}
    (hf : IsStrictEFunction f) (N : ℕ) :
    HasPowerExponentialBound N (fun z => f (z^N)) := by
  obtain ⟨C, hC, hb⟩ := strictEFunction_exponential_bound hf
  exact powerExponentialBound_power_pullback N id f C
    (lt_of_lt_of_le zero_lt_one hC) hb

/-- Actual strict E arithmetic and one-sided growth supply the determinant
normalization. The order and the leading scalar are not assumed. -/
theorem strictEFunction_origin_only_zero_exp_form {f : ℂ → ℂ}
    (hf : IsStrictEFunction f) (hnz : ∀ z, z ≠ 0 → f z ≠ 0) :
    ∃ m : ℕ, ∃ c a : AlgebraicComplex,
      ((strictEFunction_differentiable hf).analyticAt 0).meromorphicAt.order =
        ((m : ℤ) : WithTop ℤ) ∧
      c ≠ 0 ∧ (c : ℂ) = entireCauchyCoefficient f m ∧
      ∀ z, f z = (c : ℂ) * z^m * Complex.exp ((a : ℂ)*z) := by
  have hgrowth : HasPowerExponentialBound 1 f := by
    simpa only [pow_one] using strictEFunction_powerExponentialBound hf 1
  exact entire_eq_pow_subfield_exp_linear_of_one_sided_growth
    (algebraicClosure ℚ ℂ).toSubfield (strictEFunction_differentiable hf) hnz hgrowth
    (strictEFunction_entireCauchyCoefficient_mem hf)

/-- The reciprocal value at one is represented by an actual strict E-function,
now derived for the functional zero-set class. -/
theorem strictEFunction_at_one_unit_of_origin_only_zeros {f : ℂ → ℂ}
    (hf : IsStrictEFunction f) (hnz : ∀ z, z ≠ 0 → f z ≠ 0) :
    IsStrictEValueUnit (f 1) := by
  obtain ⟨m,c,a,_,hc,_,hform⟩ := strictEFunction_origin_only_zero_exp_form hf hnz
  have h1 : f 1 = (c : ℂ) * Complex.exp (a : ℂ) := by simpa using hform 1
  rw [h1]
  exact algebraic_scalar_exp_isStrictEValueUnit c a hc

/-- A nowhere-zero strict E-function itself is an algebraic scalar exponential.
This functional theorem is distinct from the unproved forward classification
for a value with a separate reciprocal representative. -/
theorem strictEFunction_nowhere_zero_exp_form {f : ℂ → ℂ}
    (hf : IsStrictEFunction f) (hnz : ∀ z, f z ≠ 0) :
    ∃ c a : AlgebraicComplex, c ≠ 0 ∧
      ∀ z, f z = (c : ℂ) * Complex.exp ((a : ℂ)*z) := by
  obtain ⟨m,c,a,_,hc,_,hform⟩ :=
    strictEFunction_origin_only_zero_exp_form hf (fun z _ => hnz z)
  have hm : m = 0 := by
    by_contra hm
    have h0 : f 0 = 0 := by simpa [zero_pow hm] using hform 0
    exact hnz 0 h0
  refine ⟨c,a,hc,fun z => ?_⟩
  simpa only [hm, pow_zero, mul_one] using hform z
end StrictEUnit
#print axioms StrictEUnit.strictEFunction_powerExponentialBound
#print axioms StrictEUnit.strictEFunction_origin_only_zero_exp_form
#print axioms StrictEUnit.strictEFunction_at_one_unit_of_origin_only_zeros
#print axioms StrictEUnit.strictEFunction_nowhere_zero_exp_form
