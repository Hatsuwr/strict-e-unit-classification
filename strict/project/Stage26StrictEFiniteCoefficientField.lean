import Stage26ODERecurrence
import Stage26StrictETaylorCoefficientField

/-!
# A fixed number field follows from the actual strict-E definition

No coefficient field or recurrence nondegeneracy is assumed here. A nonzero
formal polynomial ODE yields a nonzero recurrence; its algebraic coefficients
and finitely many exceptional initial values generate a number field. The
actual strict-E Taylor realization and rational factorial scaling then place
the defining coefficients in that field. This is a definition-translation
lemma, not a proof of the deep arithmetic lifting or E-operator theorems.
-/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- Every algebraic formal solution of a nonzero polynomial scalar ODE is
defined over one number field, together with the given ODE coefficients.
The leading polynomial may vanish at zero. -/
theorem stage26_formal_ode_finite_coefficient_field
    {K : Type*} [Field K] [CharZero K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
    (m : ℕ) (p : Fin (m + 1) → Polynomial K) (x : PowerSeries K)
    (hne : ∃ i, p i ≠ 0)
    (hode : ∑ i, (p i : PowerSeries K) *
      ((PowerSeries.derivative K)^[i.val] x) = 0) :
    ∃ F : IntermediateField ℚ K, FiniteDimensional ℚ F ∧
      (∀ n, PowerSeries.coeff K n x ∈ F) ∧ (∀ i j, (p i).coeff j ∈ F) := by
  obtain ⟨r, q, hq, hrec⟩ := stage26_finite_ode_has_recurrence m p x hne hode
  obtain ⟨F, hF, ha, _⟩ :=
    stage26_polynomial_recurrence_finite_coefficient_field_of_nonzero
      (fun n => PowerSeries.coeff K n x) r q hq ⟨0, fun n _ => hrec n⟩
  obtain ⟨E, hE, hFE, hp⟩ := stage26_finite_coefficient_field_enlarge_polynomials F hF p
  exact ⟨E, hE, fun n => hFE (ha n), hp⟩

/-- The actual strict-E predicate, without extra hypotheses, puts every
ordinary Taylor coefficient in one finite-dimensional intermediate field. -/
theorem stage26_strictE_taylor_finite_coefficient_field {f : ℂ → ℂ}
    (hf : IsStrictEFunction f) :
    ∃ F : IntermediateField ℚ AlgebraicComplex, FiniteDimensional ℚ F ∧
      ∀ n, PowerSeries.coeff AlgebraicComplex n
        (subfieldEntireTaylorAlgHom (algebraicClosure ℚ ℂ).toSubfield
          (strictEFunctionTaylorRealization f hf)) ∈ F := by
  obtain ⟨m, p, hp, hode⟩ := stage26_strictE_formal_polynomial_ode hf
  obtain ⟨F, hF, ha, _⟩ := stage26_formal_ode_finite_coefficient_field m p _ hp hode
  exact ⟨F, hF, ha⟩

/-- A fixed number field contains the factorial-normalized defining
coefficients of every actual series representation of a strict E-function.
The conclusion is uniform over the series witness, not a newly imposed input. -/
theorem stage26_strictE_fixed_coefficient_number_field {f : ℂ → ℂ}
    (hf : IsStrictEFunction f) :
    ∃ F : IntermediateField ℚ AlgebraicComplex, FiniteDimensional ℚ F ∧
      ∀ a : ℕ → AlgebraicComplex,
        (∀ z : ℂ, HasSum (fun n => (a n : ℂ) * z ^ n / (n.factorial : ℂ)) (f z)) →
        ∀ n, a n ∈ F := by
  obtain ⟨F, hF, hcoeff⟩ := stage26_strictE_taylor_finite_coefficient_field hf
  exact ⟨F, hF, fun a ha => stage26_strictE_coefficient_field_of_taylor hf F hcoeff a ha⟩

/-- An explicit fixed-field witness for the actual strict-E series and its
strict arithmetic conditions. No altered definition of strict E is used. -/
theorem stage26_strictE_fixed_field_series {f : ℂ → ℂ} (hf : IsStrictEFunction f) :
    ∃ F : IntermediateField ℚ AlgebraicComplex, FiniteDimensional ℚ F ∧
      ∃ a : ℕ → AlgebraicComplex, (∀ n, a n ∈ F) ∧
        (∀ z : ℂ, HasSum (fun n => (a n : ℂ) * z ^ n / (n.factorial : ℂ)) (f z)) ∧
        HasStrictEArithmetic a := by
  obtain ⟨F, hF, hmem⟩ := stage26_strictE_fixed_coefficient_number_field hf
  obtain ⟨a, _, hs, _, ha⟩ := hf
  exact ⟨F, hF, a, hmem a hs, hs, ha⟩

end StrictEUnit
