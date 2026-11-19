import StrictEArithmeticSeries

/-!
# The identity coordinate is a genuine strict E-function

This elementary input for Euler differentiation includes an explicit entire
series, all conjugate and positive-denominator conditions, and a nonzero
polynomial differential equation. Membership is not assumed.
-/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- The factorial coefficients of the identity coordinate. -/
def strictECoordinateCoefficient (n : ℕ) : AlgebraicComplex := if n = 1 then 1 else 0

/-- The coordinate has arithmetic constant and all common denominators equal to one. -/
theorem strictECoordinate_arithmetic : HasStrictEArithmetic strictECoordinateCoefficient := by
  refine ⟨1, le_rfl, ?_, (fun _ => 1), (fun _ => by norm_num), ?_, ?_⟩
  · intro σ n
    by_cases hn : n = 1 <;> simp [strictECoordinateCoefficient, hn]
  · intro n
    simp
  · intro n j _
    by_cases hj : j = 1
    · simpa [strictECoordinateCoefficient, hj] using strictE_natCast_isIntegral 1
    · simpa [strictECoordinateCoefficient, hj] using strictE_natCast_isIntegral 0

/-- The actual coordinate series has just its degree-one term. -/
theorem strictECoordinate_hasSum (z : ℂ) :
    HasSum (fun n => (strictECoordinateCoefficient n : ℂ) * z ^ n /
      (n.factorial : ℂ)) z := by
  have h : HasSum (fun n : ℕ => if n = 1 then z else 0) z :=
    hasSum_ite_eq 1 z
  convert h using 1
  funext n
  by_cases hn : n = 1 <;> simp [strictECoordinateCoefficient, hn]

/-- The nontrivial polynomial equation -z + z*(d/dz)z = 0. -/
theorem strictECoordinate_ode : HasAlgebraicPolynomialODE (fun z : ℂ => z) := by
  refine ⟨1, ![-1, Polynomial.X], ?_, ?_⟩
  · refine ⟨0, ?_⟩
    simp
  · intro z
    rw [Fin.sum_univ_two]
    simp [iteratedDeriv_one, deriv_id'']

/-- The actual identity polynomial satisfies every strict E-function condition. -/
theorem strictEFunction_coordinate : IsStrictEFunction (fun z : ℂ => z) :=
  ⟨strictECoordinateCoefficient, differentiable_id, strictECoordinate_hasSum,
    strictECoordinate_ode, strictECoordinate_arithmetic⟩

end StrictEUnit
