import RetainedCoefficientStrictArithmetic
import Stage41StrictSeriesRealization

noncomputable section
namespace StrictEUnit

theorem logAmplitudeFactorial_formal_series
    (p : Polynomial (LaurentSeries AlgebraicComplex)) (j : ℕ) :
    stage41_strictFormalSeries (fun n =>logAmplitudeFactorialCoefficient p j n)=
      PowerSeries.mk (fun n =>(p.coeff j).coeff (n:ℤ)) := by
  apply PowerSeries.ext
  intro n
  rw [stage41_coeff_strictFormalSeries,PowerSeries.coeff_mk]
  unfold logAmplitudeFactorialCoefficient
  have hn : (n.factorial:AlgebraicComplex)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp

/-- The actual entire factorial sum realizes the UNCHANGED natural-index
coefficient series. This statement does not assume or claim a scalar ODE. -/
theorem logAmplitudeFactorial_actual_realization
    (p : Polynomial (LaurentSeries AlgebraicComplex)) (j : ℕ)
    (ha : HasStrictEArithmetic (fun n =>logAmplitudeFactorialCoefficient p j n)) :
    Differentiable ℂ (stage41_strictSeriesFunction (fun n =>logAmplitudeFactorialCoefficient p j n)) ∧
    (∀ z : ℂ,HasSum (fun n : ℕ =>(((p.coeff j).coeff (n:ℤ):AlgebraicComplex):ℂ)*z^n)
      (stage41_strictSeriesFunction (fun n =>logAmplitudeFactorialCoefficient p j n) z)) ∧
    subfieldEntireTaylorAlgHom (algebraicClosure ℚ ℂ).toSubfield
      (stage41_strictSeriesRealization _ ha)=PowerSeries.mk (fun n =>(p.coeff j).coeff (n:ℤ)) := by
  refine ⟨stage41_strictSeries_differentiable ha,?_,?_⟩
  · intro z
    have hs := stage41_strictSeries_hasSum ha z
    have he : (fun n : ℕ =>(((p.coeff j).coeff (n:ℤ):AlgebraicComplex):ℂ)*z^n)=
        (fun n : ℕ =>(logAmplitudeFactorialCoefficient p j n:ℂ)*z^n/(n.factorial:ℂ)) := by
      funext n
      exact (logAmplitudeFactorialCoefficient_series_term (algebraicClosure ℚ ℂ).val.toRingHom p j n z).symm
    rw [he]
    exact hs
  · rw [stage41_strictSeries_taylor,logAmplitudeFactorial_formal_series]
end StrictEUnit
end
