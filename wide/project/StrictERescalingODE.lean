import StrictEFunctionDefinitions
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.CauchyIntegral

/-! Algebraic rescaling of the actual polynomial differential equation. -/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- Entire complex functions have the usual chain rule for every derivative order. -/
theorem entire_iteratedDeriv_rescale {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (α : ℂ) (n : ℕ) (z : ℂ) :
    iteratedDeriv n (fun w => f (α * w)) z = α ^ n * iteratedDeriv n f (α * z) := by
  exact congrFun (iteratedDeriv_comp_const_mul hf.contDiff α) z

/-- A nonzero algebraic change of variable preserves a nonzero polynomial. -/
theorem algebraic_polynomial_rescale_ne_zero {p : Polynomial AlgebraicComplex}
    (hp : p ≠ 0) {α : AlgebraicComplex} (hα : α ≠ 0) :
    p.comp (Polynomial.C α * Polynomial.X) ≠ 0 := by
  exact fun h => hp ((Polynomial.comp_C_mul_X_eq_zero_iff
    (mem_nonZeroDivisors_iff_ne_zero.mpr hα)).mp h)

/-- Substitution z ↦ αz, together with the inverse chain-rule factors,
transports a genuinely nonzero polynomial ODE. -/
theorem algebraicPolynomialODE_rescale {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hode : HasAlgebraicPolynomialODE f) {α : AlgebraicComplex} (hα : α ≠ 0) :
    HasAlgebraicPolynomialODE (fun z => f ((α : ℂ) * z)) := by
  obtain ⟨m, p, ⟨i, hi⟩, heq⟩ := hode
  let q : Fin (m+1) → Polynomial AlgebraicComplex := fun i =>
    Polynomial.C (α⁻¹ ^ i.val) * (p i).comp (Polynomial.C α * Polynomial.X)
  refine ⟨m, q, ⟨i, ?_⟩, ?_⟩
  · exact mul_ne_zero (Polynomial.C_ne_zero.mpr (pow_ne_zero _ (inv_ne_zero hα)))
      (algebraic_polynomial_rescale_ne_zero hi hα)
  · intro z
    convert heq ((α : ℂ) * z) using 1
    apply Finset.sum_congr rfl
    intro i _
    dsimp [q]
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_comp,
      Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X,
      entire_iteratedDeriv_rescale hf]
    change ((α : ℂ)⁻¹ ^ i.val * (p i).eval₂
      (algebraicClosure ℚ ℂ).val.toRingHom ((α : ℂ) * z)) *
      ((α : ℂ) ^ i.val * iteratedDeriv i.val f ((α : ℂ) * z)) = _
    have hαC : (α : ℂ) ≠ 0 := fun h => hα (Subtype.ext h)
    rw [inv_pow]
    field_simp
    ring

end StrictEUnit
#print axioms StrictEUnit.entire_iteratedDeriv_rescale
#print axioms StrictEUnit.algebraic_polynomial_rescale_ne_zero
#print axioms StrictEUnit.algebraicPolynomialODE_rescale
