import Stage41GeometricEntireSeries
import Stage26StrictETaylorCoefficientField

/-!
# Source strict E-series produce actual entire strict E-functions

The input is the literal algebraic coefficient sequence with strict arithmetic
and a nonzero polynomial differential operator annihilating its literal formal
factorial series. Analyticity, source matching and an actual ODE are conclusions.
The same supplied operator tuple is transported, without an ordinary-point
hypothesis at zero or an assumption that the series is nonzero.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators
namespace StrictEUnit

/-- The literal source power series, before any analytic realization. -/
def stage41_strictFormalSeries (a : ℕ → AlgebraicComplex) :
    PowerSeries AlgebraicComplex :=
  PowerSeries.mk (fun n => a n / (n.factorial : AlgebraicComplex))

@[simp] theorem stage41_coeff_strictFormalSeries (a : ℕ → AlgebraicComplex) (n : ℕ) :
    PowerSeries.coeff AlgebraicComplex n (stage41_strictFormalSeries a) =
      a n / (n.factorial : AlgebraicComplex) := by
  simp [stage41_strictFormalSeries]

/-- The actual function is defined by a tsum, not selected from a realization axiom. -/
def stage41_strictSeriesFunction (a : ℕ → AlgebraicComplex) : ℂ → ℂ :=
  exponentialGeneratingFunction (fun n => (a n : ℂ))

/-- Strict arithmetic supplies global convergence of the source series. -/
theorem stage41_strictSeries_hasSum {a : ℕ → AlgebraicComplex}
    (ha : HasStrictEArithmetic a) (z : ℂ) :
    HasSum (fun n => (a n : ℂ) * z ^ n / (n.factorial : ℂ))
      (stage41_strictSeriesFunction a z) := by
  obtain ⟨C, _, hC⟩ := strictEArithmetic_chosen_bound ha
  exact geometric_egf_hasSum _ C hC z

/-- Strict arithmetic, without any ODE, already gives entire differentiability. -/
theorem stage41_strictSeries_differentiable {a : ℕ → AlgebraicComplex}
    (ha : HasStrictEArithmetic a) :
    Differentiable ℂ (stage41_strictSeriesFunction a) := by
  obtain ⟨C, _, hC⟩ := strictEArithmetic_chosen_bound ha
  exact stage41_geometric_egf_differentiable _ C hC

/-- The actual Cauchy coefficients are the specified source coefficients. -/
theorem stage41_strictSeries_cauchyCoefficient {a : ℕ → AlgebraicComplex}
    (ha : HasStrictEArithmetic a) (n : ℕ) :
    entireCauchyCoefficient (stage41_strictSeriesFunction a) n =
      (a n : ℂ) / (n.factorial : ℂ) := by
  obtain ⟨C, _, hC⟩ := strictEArithmetic_chosen_bound ha
  exact stage41_geometric_egf_cauchyCoefficient _ C hC n

/-- The realized function belongs to the existing algebraic-Taylor entire algebra. -/
def stage41_strictSeriesRealization (a : ℕ → AlgebraicComplex)
    (ha : HasStrictEArithmetic a) :
    subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield :=
  ⟨⟨stage41_strictSeriesFunction a, stage41_strictSeries_differentiable ha⟩,
    (mem_subfieldEntireFunctionAlgebra _ _).mpr (fun n => by
      rw [stage41_strictSeries_cauchyCoefficient ha n]
      exact (algebraicClosure ℚ ℂ).toSubfield.div_mem (a n).property (natCast_mem _ _))⟩

@[simp] theorem stage41_strictSeriesRealization_apply (a : ℕ → AlgebraicComplex)
    (ha : HasStrictEArithmetic a) (z : ℂ) :
    (stage41_strictSeriesRealization a ha).val.val z = stage41_strictSeriesFunction a z := rfl

/-- Exact equality in the existing algebraic Taylor target. -/
theorem stage41_strictSeries_taylor {a : ℕ → AlgebraicComplex}
    (ha : HasStrictEArithmetic a) :
    subfieldEntireTaylorAlgHom (algebraicClosure ℚ ℂ).toSubfield
      (stage41_strictSeriesRealization a ha) = stage41_strictFormalSeries a := by
  apply PowerSeries.ext
  intro n
  apply Subtype.ext
  simpa [subfieldEntireTaylorAlgHom, subfieldEntireTaylorSeries,
    stage41_strictSeriesRealization, stage41_strictFormalSeries]
    using stage41_strictSeries_cauchyCoefficient ha n

/-- The same match after literal coefficient extension to the complex numbers. -/
theorem stage41_strictSeries_complexTaylor {a : ℕ → AlgebraicComplex}
    (ha : HasStrictEArithmetic a) :
    entireFormalTaylor (stage41_strictSeriesFunction a) =
      PowerSeries.map (algebraicClosure ℚ ℂ).val.toRingHom
        (stage41_strictFormalSeries a) := by
  ext n
  simp only [coeff_entireFormalTaylor, PowerSeries.coeff_map,
    stage41_coeff_strictFormalSeries, map_div₀, map_natCast]
  exact stage41_strictSeries_cauchyCoefficient ha n

/-- Formal and actual global polynomial differential identities are equivalent
for the exact supplied tuple, including singular operators at the origin. -/
theorem stage41_strictSeries_polynomial_ode_iff {a : ℕ → AlgebraicComplex}
    (ha : HasStrictEArithmetic a) (m : ℕ)
    (p : Fin (m + 1) → Polynomial AlgebraicComplex) :
    (∑ i, (p i : PowerSeries AlgebraicComplex) *
      (PowerSeries.derivative AlgebraicComplex :
        PowerSeries AlgebraicComplex → PowerSeries AlgebraicComplex)^[i.val]
        (stage41_strictFormalSeries a) = 0) ↔
    (∀ z : ℂ, ∑ i, (p i).eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z *
      iteratedDeriv i.val (stage41_strictSeriesFunction a) z = 0) := by
  let k := (algebraicClosure ℚ ℂ).toSubfield
  let F := stage41_strictSeriesRealization a ha
  have hmap : subfieldEntireTaylorAlgHom k
      (∑ i, Polynomial.aeval (subfieldEntireCoordinate k) (show Polynomial k from p i) *
        ((subfieldEntireFunctionDerivation k)^[i.val]) F) =
      ∑ i, (p i : PowerSeries AlgebraicComplex) *
        (PowerSeries.derivative AlgebraicComplex :
          PowerSeries AlgebraicComplex → PowerSeries AlgebraicComplex)^[i.val]
          (stage41_strictFormalSeries a) := by
    simp only [map_sum, map_mul, stage26_subfieldTaylor_polynomial,
      stage26_subfieldTaylor_iterate]
    rw [show subfieldEntireTaylorAlgHom k F = stage41_strictFormalSeries a from
      stage41_strictSeries_taylor ha]
    rfl
  rw [← hmap]
  constructor
  · intro h
    have hactual := (subfieldEntireTaylorAlgHom_injective k)
      (h.trans (map_zero (subfieldEntireTaylorAlgHom k)).symm)
    exact (stage14_actualPolynomialRelation_iff k F m p).mp hactual
  · intro h
    rw [(stage14_actualPolynomialRelation_iff k F m p).mpr h, map_zero]

/-- The source-facing definition uses arithmetic and a genuinely nonzero formal
operator, with no analytic or actual-function premise. -/
def Stage41IsStrictESeries (a : ℕ → AlgebraicComplex) : Prop :=
  HasStrictEArithmetic a ∧
    ∃ m : ℕ, ∃ p : Fin (m + 1) → Polynomial AlgebraicComplex,
      (∃ i, p i ≠ 0) ∧
      ∑ i, (p i : PowerSeries AlgebraicComplex) *
        (PowerSeries.derivative AlgebraicComplex :
          PowerSeries AlgebraicComplex → PowerSeries AlgebraicComplex)^[i.val]
          (stage41_strictFormalSeries a) = 0

/-- The full converse: formal strict-E data produce the unchanged actual
IsStrictEFunction predicate for the constructed global factorial sum. -/
theorem stage41_strictSeries_isStrictEFunction {a : ℕ → AlgebraicComplex}
    (ha : Stage41IsStrictESeries a) :
    IsStrictEFunction (stage41_strictSeriesFunction a) := by
  obtain ⟨harith, m, p, hp, hode⟩ := ha
  exact ⟨a, stage41_strictSeries_differentiable harith,
    stage41_strictSeries_hasSum harith,
    ⟨m, p, hp, (stage41_strictSeries_polynomial_ode_iff harith m p).mp hode⟩, harith⟩

/-- Explicit-input form of the converse, retaining the exact given operator. -/
theorem stage41_strictSeries_realization_of_formal_ode
    (a : ℕ → AlgebraicComplex) (ha : HasStrictEArithmetic a)
    (m : ℕ) (p : Fin (m + 1) → Polynomial AlgebraicComplex)
    (hp : ∃ i, p i ≠ 0)
    (hode : ∑ i, (p i : PowerSeries AlgebraicComplex) *
      (PowerSeries.derivative AlgebraicComplex :
        PowerSeries AlgebraicComplex → PowerSeries AlgebraicComplex)^[i.val]
        (stage41_strictFormalSeries a) = 0) :
    IsStrictEFunction (stage41_strictSeriesFunction a) ∧
    (∀ z : ℂ, HasSum (fun n => (a n : ℂ) * z ^ n / (n.factorial : ℂ))
      (stage41_strictSeriesFunction a z)) ∧
    (subfieldEntireTaylorAlgHom (algebraicClosure ℚ ℂ).toSubfield
      (stage41_strictSeriesRealization a ha) = stage41_strictFormalSeries a) ∧
    (∀ z : ℂ, ∑ i, (p i).eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z *
      iteratedDeriv i.val (stage41_strictSeriesFunction a) z = 0) :=
  ⟨stage41_strictSeries_isStrictEFunction ⟨ha, m, p, hp, hode⟩,
    stage41_strictSeries_hasSum ha, stage41_strictSeries_taylor ha,
    (stage41_strictSeries_polynomial_ode_iff ha m p).mp hode⟩

end StrictEUnit
