import AlgebraicScalarExponential

/-!
Arithmetic closure under algebraic rescaling of the argument. The intermediate
coefficientwise product lemma preserves bounds for every embedding and uses the
product of positive natural common denominators, for every initial segment.
-/
noncomputable section
namespace StrictEUnit

/-- Coefficientwise products preserve the full strict E arithmetic conditions.
This is an arithmetic statement, not a claim about products of E-functions. -/
theorem strictEArithmetic_mul_for_rescaling {a b : ℕ → AlgebraicComplex}
    (ha : HasStrictEArithmetic a) (hb : HasStrictEArithmetic b) :
    HasStrictEArithmetic (fun n => a n * b n) := by
  obtain ⟨A, hA, hca, da, hda, hba, hia⟩ := ha
  obtain ⟨B, hB, hcb, db, hdb, hbb, hib⟩ := hb
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  refine ⟨A * B, (by nlinarith), ?_, (fun n => da n * db n), ?_, ?_, ?_⟩
  · intro σ n
    simp only [map_mul, norm_mul, mul_pow]
    exact mul_le_mul (hca σ n) (hcb σ n) (norm_nonneg _) (pow_nonneg hA0 _)
  · intro n
    exact Nat.mul_pos (hda n) (hdb n)
  · intro n
    simp only [Nat.cast_mul, mul_pow]
    exact mul_le_mul (hba n) (hbb n) (Nat.cast_nonneg _) (pow_nonneg hA0 _)
  · intro n j hj
    have hi := (hia n j hj).mul (hib n j hj)
    convert hi using 1
    simp only [Nat.cast_mul, IntermediateField.coe_mul]
    ring

/-- Multiplying the nth coefficient by the nth power of any algebraic number
preserves both all-conjugate geometric bounds and exponentially bounded,
positive integer common denominators. The rescaling factor may be zero. -/
theorem strictEArithmetic_rescale {a : ℕ → AlgebraicComplex}
    (ha : HasStrictEArithmetic a) (α : AlgebraicComplex) :
    HasStrictEArithmetic (fun n => a n * α ^ n) := by
  have hα : HasStrictEArithmetic (fun n => α ^ n) := by
    simpa only [one_mul] using algebraic_scalar_exp_arithmetic 1 α
  exact strictEArithmetic_mul_for_rescaling ha hα

end StrictEUnit
#print axioms StrictEUnit.strictEArithmetic_mul_for_rescaling
#print axioms StrictEUnit.strictEArithmetic_rescale
