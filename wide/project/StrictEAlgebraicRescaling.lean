import StrictERescalingODE
import StrictERescalingArithmetic

/-!
# Algebraic rescaling and normalization of strict E-values

The closure result preserves the existing full definition, including its actual
factorial series, entire differentiability, genuinely nonzero algebraic ODE,
and all-conjugate/common-integer-denominator bounds. Evaluation at one is a
consequence, not a replacement definition of a strict E-value.
-/
noncomputable section
namespace StrictEUnit

/-- Substituting an algebraic scalar into an actual factorial series multiplies
its nth algebraic coefficient by the nth power of that scalar. -/
theorem strictE_series_rescale {a : ℕ → AlgebraicComplex} {f : ℂ → ℂ}
    (hs : ∀ z : ℂ, HasSum (fun n => (a n : ℂ) * z ^ n / (n.factorial : ℂ)) (f z))
    (α : AlgebraicComplex) (z : ℂ) :
    HasSum (fun n => ((a n * α ^ n : AlgebraicComplex) : ℂ) * z ^ n /
      (n.factorial : ℂ)) (f ((α : ℂ) * z)) := by
  convert hs ((α : ℂ) * z) using 1
  funext n
  simp only [IntermediateField.coe_mul, IntermediateField.coe_pow, mul_pow]
  ring

/-- The full strict E-function class is closed under every algebraic rescaling,
including zero. The zero case uses algebraicity of the actual value at zero. -/
theorem strictEFunction_rescale {f : ℂ → ℂ} (hf : IsStrictEFunction f)
    (α : AlgebraicComplex) : IsStrictEFunction (fun z => f ((α : ℂ) * z)) := by
  by_cases hα : α = 0
  · have hconst := (constant_isStrictEFunction_iff (f 0)).mpr
      (strictEFunction_zero_isAlgebraic hf)
    simpa only [hα, IntermediateField.coe_zero, zero_mul] using hconst
  · obtain ⟨a, hdiff, hs, hode, ha⟩ := hf
    refine ⟨(fun n => a n * α ^ n), ?_, strictE_series_rescale hs α,
      algebraicPolynomialODE_rescale hdiff hode hα, strictEArithmetic_rescale ha α⟩
    exact hdiff.comp ((differentiable_const (α : ℂ)).mul differentiable_id)

/-- Nonzero algebraic rescaling is reversible inside the full function class. -/
theorem strictEFunction_rescale_iff {f : ℂ → ℂ} {α : AlgebraicComplex} (hα : α ≠ 0) :
    IsStrictEFunction (fun z => f ((α : ℂ) * z)) ↔ IsStrictEFunction f := by
  constructor
  · intro h
    have hinv := strictEFunction_rescale h α⁻¹
    have hαC : (α : ℂ) ≠ 0 := fun h => hα (Subtype.ext h)
    simpa only [IntermediateField.coe_inv, ← mul_assoc, mul_inv_cancel₀ hαC, one_mul] using hinv
  · intro h
    exact strictEFunction_rescale h α

/-- Every strict E-value can genuinely be evaluated at one after algebraic
rescaling of a strict E-function. -/
theorem strictEValue_iff_at_one (u : ℂ) :
    IsStrictEValue u ↔ ∃ f : ℂ → ℂ, IsStrictEFunction f ∧ f 1 = u := by
  constructor
  · rintro ⟨f, hf, α, hα⟩
    refine ⟨(fun z => f ((α : ℂ) * z)), strictEFunction_rescale hf α, ?_⟩
    simpa only [mul_one] using hα
  · rintro ⟨f, hf, hu⟩
    exact ⟨f, hf, 1, by simpa only [IntermediateField.coe_one] using hu⟩

/-- Numerical strict E-unit membership has normalized representatives for both
the value and its reciprocal. It still assumes no unproved ring structure. -/
theorem strictEValueUnit_iff_at_one (u : ℂ) :
    IsStrictEValueUnit u ↔ u ≠ 0 ∧
      (∃ f : ℂ → ℂ, IsStrictEFunction f ∧ f 1 = u) ∧
      (∃ g : ℂ → ℂ, IsStrictEFunction g ∧ g 1 = u⁻¹) := by
  simp only [IsStrictEValueUnit, strictEValue_iff_at_one]

end StrictEUnit
#print axioms StrictEUnit.strictE_series_rescale
#print axioms StrictEUnit.strictEFunction_rescale
#print axioms StrictEUnit.strictEFunction_rescale_iff
#print axioms StrictEUnit.strictEValue_iff_at_one
#print axioms StrictEUnit.strictEValueUnit_iff_at_one
