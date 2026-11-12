import StrictEValueUnitClassification

set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000

#check @StrictEUnit.strictEValueUnit_iff_algebraic_scalar_exp
#print axioms StrictEUnit.strictEValueUnit_iff_algebraic_scalar_exp
#print axioms StrictEUnit.actualStrictE_commonArithmeticFrameAvailability
#print axioms StrictEUnit.strictELaurentRelationLifting

example (u : ℂ) : StrictEUnit.IsStrictEValueUnit u ↔
    ∃ α β : ℂ, IsAlgebraic ℚ α ∧ α ≠ 0 ∧ IsAlgebraic ℚ β ∧
      u = α * Complex.exp β :=
  StrictEUnit.strictEValueUnit_iff_algebraic_scalar_exp u
