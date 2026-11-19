import Stage15StrictEDerivativeClosure
import Stage15StrictECoordinate
import Stage14StrictERingClosure

/-!
# Full strict E-function closure under Euler differentiation

Euler differentiation is the actual operator f ↦ (z ↦ z * deriv f z).
The coordinate is independently proved strict E, and actual product closure
retains all arithmetic, analytic-series, and nonzero polynomial-ODE clauses.
-/
noncomputable section
namespace StrictEUnit

/-- The actual Euler derivative z*f'(z) is a full strict E-function. -/
theorem strictEFunction_eulerDerivative {f : ℂ → ℂ} (hf : IsStrictEFunction f) :
    IsStrictEFunction (fun z => z * deriv f z) :=
  strictEFunction_mul strictEFunction_coordinate (strictEFunction_derivative hf)

/-- Repeated actual Euler differentiation preserves all strict E conditions. -/
theorem strictEFunction_iteratedEulerDerivative {f : ℂ → ℂ}
    (hf : IsStrictEFunction f) (r : ℕ) :
    IsStrictEFunction (((fun g : ℂ → ℂ => fun z => z * deriv g z)^[r]) f) := by
  induction r with
  | zero => exact hf
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    exact strictEFunction_eulerDerivative ih

/-- Derivative values at algebraic arguments are actual strict E-values. -/
theorem strictEFunction_derivative_isStrictEValue {f : ℂ → ℂ}
    (hf : IsStrictEFunction f) (α : AlgebraicComplex) : IsStrictEValue (deriv f α) :=
  ⟨deriv f, strictEFunction_derivative hf, α, rfl⟩

/-- Euler derivative values at algebraic arguments are actual strict E-values. -/
theorem strictEFunction_eulerDerivative_isStrictEValue {f : ℂ → ℂ}
    (hf : IsStrictEFunction f) (α : AlgebraicComplex) :
    IsStrictEValue ((α : ℂ) * deriv f α) :=
  ⟨(fun z => z * deriv f z), strictEFunction_eulerDerivative hf, α, rfl⟩

end StrictEUnit
