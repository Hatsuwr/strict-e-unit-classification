import ReverseBorelPolynomialODE
import Stage26StrictEFiniteCoefficientField

/-! NEW SOURCE-ONLY, UNCOMPILED. This attachment retains the actual ordinary
Borel ODE tuple and one common finite coefficient field. Arithmetic is copied
from the input, not proved anew. No minimal-operator, regularity, or arithmetic
local-basis assertion is made. -/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- Literal ordinary-series differential data and the unchanged arithmetic
predicate live over one common finite coefficient field. -/
theorem stage41_ordinary_borel_joint_data
    (a : ℕ → AlgebraicComplex) (ha : Stage41IsStrictESeries a) :
    ∃ m : ℕ, ∃ p : Fin (m+1) → Polynomial AlgebraicComplex,
      ∃ F : IntermediateField ℚ AlgebraicComplex,
        (∃ i, p i ≠ 0) ∧
        (∑ i, (p i : PowerSeries AlgebraicComplex) *
          (PowerSeries.derivative AlgebraicComplex)^[i.val] (PowerSeries.mk a)) = 0 ∧
        FiniteDimensional ℚ F ∧
        (∀ n, a n ∈ F) ∧
        (∀ i j, (p i).coeff j ∈ F) ∧
        HasStrictEArithmetic a := by
  obtain ⟨m, p, hp, hode⟩ := stage41_ordinary_borel_polynomial_ode a ha
  obtain ⟨F, hF, haF, hpF⟩ :=
    stage26_formal_ode_finite_coefficient_field m p (PowerSeries.mk a) hp hode
  refine ⟨m, p, F, hp, hode, hF, ?_, hpF, ha.1⟩
  intro n
  simpa only [PowerSeries.coeff_mk] using haF n

end StrictEUnit
end
