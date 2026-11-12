import OrdinaryBorelMinimalCyclic
import Stage41StrictSeriesCorrespondence

/-! Minimal cyclic data for the actual factorial-normalized E-function Taylor
series, distinct from the ordinary Borel transform. No ordinariness theorem
or arithmetic estimates for this minimal companion are asserted. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators
namespace StrictEUnit

theorem stage41_strictFormalSeries_laurent_ne_zero
    (a : ℕ → AlgebraicComplex) (hne : ∃ n, a n ≠ 0) :
    HahnSeries.ofPowerSeries ℤ AlgebraicComplex (stage41_strictFormalSeries a) ≠ 0 := by
  have hnormalized : ∃ n, a n / (n.factorial : AlgebraicComplex) ≠ 0 := by
    obtain ⟨n, hn⟩ := hne
    exact ⟨n, div_ne_zero hn (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))⟩
  simpa only [stage41_strictFormalSeries] using
    (ordinaryBorel_laurent_mk_ne_zero
      (fun n => a n / (n.factorial : AlgebraicComplex)) hnormalized)

theorem stage41_strictFormalSeries_laurent_scalar_relation
    (a : ℕ → AlgebraicComplex) (ha : Stage41IsStrictESeries a) :
    HasScalarLinearDifferentialRelation (B := RatFunc AlgebraicComplex)
      (stage14_laurentAlgebraDerivation (k := AlgebraicComplex))
      (HahnSeries.ofPowerSeries ℤ AlgebraicComplex (stage41_strictFormalSeries a)) := by
  obtain ⟨m, p, hp, hode⟩ := ha.2
  exact ordinaryBorel_laurent_scalar_relation (stage41_strictFormalSeries a) m p hp hode

/-- The predicate's historical Borel name is generic in its argument; here its
input is precisely the factorial-normalized series. -/
theorem stage41_strictFormalSeries_exists_minimal_cyclic
    (a : ℕ → AlgebraicComplex) (ha : Stage41IsStrictESeries a)
    (hne : ∃ n, a n ≠ 0) :
    ∃ r, 0 < r ∧ ∃ b : Fin r → RatFunc AlgebraicComplex,
      OrdinaryBorelMinimalCyclicData
        (HahnSeries.ofPowerSeries ℤ AlgebraicComplex (stage41_strictFormalSeries a)) r b := by
  exact ordinaryBorel_exists_minimal_cyclic
    (HahnSeries.ofPowerSeries ℤ AlgebraicComplex (stage41_strictFormalSeries a))
    (stage41_strictFormalSeries_laurent_ne_zero a hne)
    (stage41_strictFormalSeries_laurent_scalar_relation a ha)

theorem strictEFunctionTaylorRealization_eq_strictFormalSeries
    {f : ℂ → ℂ} (hf : IsStrictEFunction f) (a : ℕ → AlgebraicComplex)
    (hs : ∀ z : ℂ,
      HasSum (fun n => (a n : ℂ) * z ^ n / (n.factorial : ℂ)) (f z)) :
    subfieldEntireTaylorAlgHom (algebraicClosure ℚ ℂ).toSubfield
      (strictEFunctionTaylorRealization f hf) = stage41_strictFormalSeries a := by
  apply PowerSeries.ext
  intro n
  exact (stage26_strictE_taylor_coefficient hf a hs n).trans
    (stage41_coeff_strictFormalSeries a n).symm

/-- All coefficient and representation witnesses are extracted from the actual
strict-E input, not supplied as extra hypotheses. -/
theorem strictEFunction_exists_exact_factorial_minimal_cyclic
    {f : ℂ → ℂ} (hf : IsStrictEFunction f) (hne : f ≠ 0) :
    ∃ a : ℕ → AlgebraicComplex,
      Stage41IsStrictESeries a ∧
      (∀ z : ℂ, HasSum (fun n => (a n : ℂ) * z ^ n / (n.factorial : ℂ)) (f z)) ∧
      stage41_strictSeriesFunction a = f ∧
      (subfieldEntireTaylorAlgHom (algebraicClosure ℚ ℂ).toSubfield
        (strictEFunctionTaylorRealization f hf) = stage41_strictFormalSeries a) ∧
      (∃ r, 0 < r ∧ ∃ b : Fin r → RatFunc AlgebraicComplex,
        OrdinaryBorelMinimalCyclicData
          (HahnSeries.ofPowerSeries ℤ AlgebraicComplex (stage41_strictFormalSeries a)) r b) := by
  classical
  have hcopy := hf
  obtain ⟨a, hent, hs, hode, harith⟩ := hcopy
  have hseries : Stage41IsStrictESeries a := stage41_actualStrictE_isStrictESeries hf a hs
  have hcoeff : ∃ n, a n ≠ 0 := by
    by_contra h
    have hz : ∀ n, a n = 0 := by
      intro n
      by_contra hn
      exact h ⟨n, hn⟩
    apply hne
    funext z
    calc
      f z = ∑' n : ℕ, (a n : ℂ) * z ^ n / (n.factorial : ℂ) := (hs z).tsum_eq.symm
      _ = 0 := by simp [hz]
  exact ⟨a, hseries, hs,
    stage41_strictSeriesFunction_eq_of_representation harith f hs,
    strictEFunctionTaylorRealization_eq_strictFormalSeries hf a hs,
    stage41_strictFormalSeries_exists_minimal_cyclic a hseries hcoeff⟩

/-- Direct actual-input endpoint in the existing injective differential Laurent
image. This is the minimal companion of the original function's Taylor series. -/
theorem strictEFunction_exists_actualLaurent_minimal_cyclic
    {f : ℂ → ℂ} (hf : IsStrictEFunction f) (hne : f ≠ 0) :
    ∃ r, 0 < r ∧ ∃ b : Fin r → RatFunc AlgebraicComplex,
      OrdinaryBorelMinimalCyclicData
        (stage14_subfieldEntireLaurentAlgHom (algebraicClosure ℚ ℂ).toSubfield
          (strictEFunctionTaylorRealization f hf)) r b := by
  obtain ⟨a, hseries, hs, hactual, htaylor, hminimal⟩ :=
    strictEFunction_exists_exact_factorial_minimal_cyclic hf hne
  simpa only [stage14_subfieldEntireLaurentAlgHom_apply, htaylor] using hminimal
end StrictEUnit
