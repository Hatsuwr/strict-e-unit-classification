import V5FiniteSystemEndpoint136
import V5ActualReciprocalExponential140

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 1800
namespace StrictEUnit

/-- Wide E-value unit classification from the constructed actual Fin-system endpoint. -/
theorem v5_wide_unit_classification140 (u : ℂ) :
    V5IsWideEValueUnit131 u ↔
      ∃ α β : ℂ, IsAlgebraic ℚ α ∧ α ≠ 0 ∧ IsAlgebraic ℚ β ∧
        u = α * Complex.exp β := by
  apply v5_wide_eunit_iff_of_at_one131
  apply v5_wide_reciprocal_of_finite_system136
  intro r F A hf hA i j hij
  exact v5ActualReciprocalExponential140 F A hf hA i j hij

theorem v5_wide_reciprocal_at_one140 : V5WideReciprocalAtOne131 := by
  apply v5_wide_reciprocal_of_finite_system136
  intro r F A hf hA i j hij
  exact v5ActualReciprocalExponential140 F A hf hA i j hij

end StrictEUnit
#print axioms StrictEUnit.v5_wide_unit_classification140

#print axioms StrictEUnit.v5_wide_reciprocal_at_one140
