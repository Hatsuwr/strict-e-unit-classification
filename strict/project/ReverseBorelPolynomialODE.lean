import ReverseBorelRecurrenceCore
import UniformFallingFactorialExpansion

/-! NEW SOURCE-ONLY, UNCOMPILED. The uniform expansion dependency is being
prepared independently. The endpoint is an actual nonzero polynomial ODE for
the literal ordinary generating series; no global G-operator classification,
regularity or arithmetic Frobenius-family existence is claimed. -/
noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Every nonzero finite polynomial recurrence gives a nonzero polynomial
ordinary differential relation for the SAME ordinary PowerSeries.mk a. -/
theorem polynomial_recurrence_ordinary_series_ode
    (a : ℕ → K) (r : ℕ) (Q : Fin (r+1) → Polynomial K)
    (hQ : ∃ j, Q j ≠ 0)
    (hrec : ∀ n : ℕ, (∑ j, (Q j).eval (n : K) * a (n+j.val)) = 0) :
    ∃ m : ℕ, ∃ p : Fin (m+1) → Polynomial K,
      (∃ i, p i ≠ 0) ∧ (∑ i, (p i : PowerSeries K) *
        (PowerSeries.derivative K)^[i.val] (PowerSeries.mk a)) = 0 := by
  obtain ⟨L,b,hb⟩ := exists_uniform_descPochhammer_expansion r
    (fun j : Fin (r+1) => Q j * borelFactorialMultiplier j.val (r-j.val))
  exact ⟨r+L, borelNormalTuple r L b,
    recurrence_to_ordinary_ode_of_expansion a r Q hQ hrec L b hb⟩

/-- Borel coefficient bridge: the original Stage41 strict factorial series
has an ordinary generating series with a genuine polynomial differential ODE.
This changes neither its coefficient sequence nor its arithmetic predicate. -/
theorem stage41_ordinary_borel_polynomial_ode
    (a : ℕ → AlgebraicComplex) (ha : Stage41IsStrictESeries a) :
    ∃ m : ℕ, ∃ p : Fin (m+1) → Polynomial AlgebraicComplex,
      (∃ i, p i ≠ 0) ∧ (∑ i, (p i : PowerSeries AlgebraicComplex) *
        (PowerSeries.derivative AlgebraicComplex)^[i.val] (PowerSeries.mk a)) = 0 := by
  obtain ⟨r,Q,hQ,hrec⟩ := stage41_original_coefficients_polynomial_recurrence a ha
  exact polynomial_recurrence_ordinary_series_ode a r Q hQ hrec

end StrictEUnit
end
