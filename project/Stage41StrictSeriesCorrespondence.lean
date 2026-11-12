import Stage41StrictSeriesRealization
import Stage26StrictEFiniteCoefficientField

/-!
# Exact equivalence of source and actual strict E-series

The new source predicate is equivalent to existence of an actual strict
E-function represented by that same series. The given formal operator also
places all coefficients and operator coefficients in one number field.
Neither statement identifies a published E-operator solution basis.
-/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- Two global factorial-series representations of the same entire function
have identical algebraic coefficients, without an arithmetic premise. -/
theorem stage41_factorialSeries_coefficients_unique {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (a b : ℕ → AlgebraicComplex)
    (ha : ∀ z : ℂ, HasSum (fun n => (a n : ℂ) * z ^ n / (n.factorial : ℂ)) (f z))
    (hb : ∀ z : ℂ, HasSum (fun n => (b n : ℂ) * z ^ n / (n.factorial : ℂ)) (f z)) : a = b := by
  have hc (c : ℕ → AlgebraicComplex)
      (hs : ∀ z : ℂ, HasSum (fun n => (c n : ℂ) * z ^ n / (n.factorial : ℂ)) (f z))
      (n : ℕ) : entireCauchyCoefficient f n = (c n : ℂ) / (n.factorial : ℂ) := by
    apply entireCauchyCoefficient_eq_of_hasSum hf
    intro z
    convert hs z using 1
    funext j
    ring
  funext n
  apply Subtype.ext
  have h := (hc a ha n).symm.trans (hc b hb n)
  exact (div_left_inj' (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))).mp h

/-- Any supplied source representation of an actual strict E-function satisfies
all source strict-E conditions, including the formal ODE for its exact coefficients. -/
theorem stage41_actualStrictE_isStrictESeries {f : ℂ → ℂ}
    (hf : IsStrictEFunction f) (a : ℕ → AlgebraicComplex)
    (ha : ∀ z : ℂ, HasSum (fun n => (a n : ℂ) * z ^ n / (n.factorial : ℂ)) (f z)) :
    Stage41IsStrictESeries a := by
  obtain ⟨b, hbent, hbs, _, hbarith⟩ := hf
  have hab := stage41_factorialSeries_coefficients_unique hbent a b ha hbs
  have harith : HasStrictEArithmetic a := hab ▸ hbarith
  have hfull : IsStrictEFunction f := by
    exact ⟨b, hbent, hbs, by assumption, hbarith⟩
  obtain ⟨m, p, hp, hode⟩ := stage26_strictE_formal_polynomial_ode hfull
  refine ⟨harith, m, p, hp, ?_⟩
  have ht : subfieldEntireTaylorAlgHom (algebraicClosure ℚ ℂ).toSubfield
      (strictEFunctionTaylorRealization f hfull) = stage41_strictFormalSeries a := by
    apply PowerSeries.ext
    intro n
    exact (stage26_strictE_taylor_coefficient hfull a ha n).trans
      (stage41_coeff_strictFormalSeries a n).symm
  rwa [ht] at hode

/-- Exact definition bridge in both directions. The right-hand representation
uses the same sequence a, not merely some existential strict-E coefficients. -/
theorem stage41_strictESeries_iff_actual_representation (a : ℕ → AlgebraicComplex) :
    Stage41IsStrictESeries a ↔
      ∃ f : ℂ → ℂ, IsStrictEFunction f ∧
        ∀ z : ℂ, HasSum (fun n => (a n : ℂ) * z ^ n / (n.factorial : ℂ)) (f z) := by
  constructor
  · intro ha
    exact ⟨stage41_strictSeriesFunction a, stage41_strictSeries_isStrictEFunction ha,
      stage41_strictSeries_hasSum ha.1⟩
  · rintro ⟨f, hf, hs⟩
    exact stage41_actualStrictE_isStrictESeries hf a hs

/-- A source series has exactly one represented actual function; the construction
is that function on the whole complex plane. -/
theorem stage41_strictSeriesFunction_eq_of_representation {a : ℕ → AlgebraicComplex}
    (ha : HasStrictEArithmetic a) (f : ℂ → ℂ)
    (hs : ∀ z : ℂ, HasSum (fun n => (a n : ℂ) * z ^ n / (n.factorial : ℂ)) (f z)) :
    stage41_strictSeriesFunction a = f := by
  funext z
  exact (stage41_strictSeries_hasSum ha z).unique (hs z)

/-- The existing Stage26 singular-ODE recurrence theorem also applies directly
to the source data: one number field contains all coefficients and the entire
supplied operator tuple. No extra fixed-field premise is introduced. -/
theorem stage41_formalStrictSeries_fixed_numberField
    (a : ℕ → AlgebraicComplex) (m : ℕ)
    (p : Fin (m + 1) → Polynomial AlgebraicComplex) (hp : ∃ i, p i ≠ 0)
    (hode : ∑ i, (p i : PowerSeries AlgebraicComplex) *
      (PowerSeries.derivative AlgebraicComplex : PowerSeries AlgebraicComplex →
        PowerSeries AlgebraicComplex)^[i.val] (stage41_strictFormalSeries a) = 0) :
    ∃ F : IntermediateField ℚ AlgebraicComplex, FiniteDimensional ℚ F ∧
      (∀ n, a n ∈ F) ∧ (∀ i j, (p i).coeff j ∈ F) := by
  obtain ⟨F, hF, ha, hpc⟩ :=
    stage26_formal_ode_finite_coefficient_field m p (stage41_strictFormalSeries a) hp hode
  refine ⟨F, hF, fun n => ?_, hpc⟩
  apply (stage26_factorial_normalization_mem_iff F a n).mp
  simpa only [stage41_coeff_strictFormalSeries] using ha n

end StrictEUnit
