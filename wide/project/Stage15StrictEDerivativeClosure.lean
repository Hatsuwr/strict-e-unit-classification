import Stage15StrictEDerivativeSeries
import Stage15DifferentialDerivativeClosure
import Stage14ActualAnalyticODETransfer

/-!
# Full strict E-function closure under the actual derivative

Every defining clause is proved: the derivative is entire, its actual global
factorial series has shifted coefficients, those coefficients satisfy the full
arithmetic predicate, and the derivative has a genuinely nonzero polynomial ODE.
-/
noncomputable section
namespace StrictEUnit

/-- Derivative ODE closure for actual entire functions with Taylor coefficients
in the chosen subfield, transferred back from the concrete Laurent field. -/
theorem stage15_actualSubfieldODE_derivative (k : Subfield ℂ)
    (f : subfieldEntireFunctionAlgebra k)
    (hf : HasSubfieldPolynomialODE k f.val.val) :
    HasSubfieldPolynomialODE k (deriv f.val.val) := by
  change HasSubfieldPolynomialODE k (subfieldEntireFunctionDerivation k f).val.val
  apply (stage14_actualODE_iff_laurentODE k (subfieldEntireFunctionDerivation k f)).mpr
  rw [stage14_subfieldEntireLaurentAlgHom_derivation]
  exact stage15_laurentPolynomialODE_derivative
    ((stage14_actualODE_iff_laurentODE k f).mp hf)

/-- A strict E-function's actual derivative satisfies a nonzero algebraic
polynomial differential equation on the entire complex plane. -/
theorem strictEFunction_derivative_hasAlgebraicPolynomialODE {f : ℂ → ℂ}
    (hf : IsStrictEFunction f) : HasAlgebraicPolynomialODE (deriv f) := by
  apply (stage14_algebraicPolynomialODE_iff_subfield _).mpr
  apply stage15_actualSubfieldODE_derivative (algebraicClosure ℚ ℂ).toSubfield
    (strictEFunctionTaylorRealization f hf)
  exact (stage14_algebraicPolynomialODE_iff_subfield f).mp hf.choose_spec.2.2.1

/-- Full closure under complex differentiation, with no extra hypothesis. -/
theorem strictEFunction_derivative {f : ℂ → ℂ} (hf : IsStrictEFunction f) :
    IsStrictEFunction (deriv f) := by
  have ho := strictEFunction_derivative_hasAlgebraicPolynomialODE hf
  obtain ⟨a, hd, hs, _, ha⟩ := hf
  refine ⟨(fun n => a (n + 1)),
    differentiableOn_univ.mp (hd.differentiableOn.deriv isOpen_univ),
    strictE_egf_hasSum_derivative hd hs, ho, strictEArithmetic_derivative ha⟩

/-- Every genuine iterated complex derivative is again a full strict E-function. -/
theorem strictEFunction_iteratedDeriv {f : ℂ → ℂ} (hf : IsStrictEFunction f) (r : ℕ) :
    IsStrictEFunction (iteratedDeriv r f) := by
  induction r with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ r ih =>
    rw [iteratedDeriv_succ]
    exact strictEFunction_derivative ih

end StrictEUnit
