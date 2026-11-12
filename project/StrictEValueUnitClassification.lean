import ActualStrictEFrameAvailability
import GeneralStrictEMinimalNonvanishing
import Stage25ConditionalStrictEUnitClassification

/-! Unconditional numerical classification for the original strict-E value
predicate. Both formerly separate arithmetic inputs are the proved original
assertions; neither is retained as a hypothesis of the final theorem. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit

/-- The original numerical unit criterion, with both arithmetic inputs proved. -/
theorem strictEValueUnit_iff_algebraic_scalar_exp (u : ℂ) :
    IsStrictEValueUnit u ↔
      ∃ α β : ℂ, IsAlgebraic ℚ α ∧ α ≠ 0 ∧ IsAlgebraic ℚ β ∧
        u = α * Complex.exp β :=
  strictEValueUnit_iff_algebraic_scalar_exp_of_arithmetic_inputs
    actualStrictE_commonArithmeticFrameAvailability strictELaurentRelationLifting u

end StrictEUnit
end
