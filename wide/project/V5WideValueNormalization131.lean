import V5BroadActualData
import StrictEAlgebraicRescaling

noncomputable section
namespace StrictEUnit

/-- Algebraic argument rescaling keeps the same prescribed wide exponent. -/
theorem v5_broad_arithmetic_rescale131 {a : ℕ → AlgebraicComplex}
    (ha : V5BroadAlgebraicArithmetic a) (b : AlgebraicComplex) :
    V5BroadAlgebraicArithmetic (fun n => a n * b ^ n) := by
  have hb : HasStrictEArithmetic (fun n => b ^ n) := by
    simpa only [one_mul] using algebraic_scalar_exp_arithmetic 1 b
  obtain ⟨B,hB,hcb,db,hdb,hbb,hib⟩ := hb
  intro ε hε
  obtain ⟨A,hA,da,hda,hba,hca,hia⟩ := ha ε hε
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  refine ⟨A * B, by nlinarith, (fun n => da n * db n), ?_, ?_, ?_, ?_⟩
  · intro n
    exact Nat.mul_pos (hda n) (hdb n)
  · intro n
    simp only [Nat.cast_mul, mul_pow]
    calc
      (da n : ℝ) * (db n : ℝ) ≤
          (A^(n+1) * (n.factorial : ℝ)^ε) * B^(n+1) :=
        mul_le_mul (hba n) (hbb n) (Nat.cast_nonneg _) (by positivity)
      _ = _ := by ring
  · intro σ n
    simp only [map_mul, norm_mul, mul_pow]
    calc
      ‖σ (a n)‖ * ‖σ (b ^ n)‖ ≤
          (A^(n+1) * (n.factorial : ℝ)^ε) * B^(n+1) :=
        mul_le_mul (hca σ n) (hcb σ n) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · intro n j hj
    have hi := (hia n j hj).mul (hib n j hj)
    convert hi using 1
    simp only [Nat.cast_mul, IntermediateField.coe_mul]
    ring

/-- Wide E-functions may be evaluated at algebraic arguments by rescaling to 1. -/
theorem v5_broad_function_rescale131 {f : ℂ → ℂ} (hf : V5IsBroadEFunction f)
    (b : AlgebraicComplex) : V5IsBroadEFunction (fun z => f ((b : ℂ) * z)) := by
  obtain ⟨a, hdiff, hs, hode, ha⟩ := hf
  by_cases hb : b = 0
  · have h0 : (a 0 : ℂ) = f 0 := by
      symm
      apply (hs 0).unique
      convert hasSum_ite_eq 0 ((a 0 : ℂ)) using 1
      funext n
      by_cases hn : n = 0
      · simp [hn]
      · simp [hn]
    have hc := v5_strict_is_broad (algebraic_constant_isStrictEFunction (a 0))
    simpa only [hb, IntermediateField.coe_zero, zero_mul, h0] using hc
  · refine ⟨(fun n => a n * b ^ n), ?_, strictE_series_rescale hs b,
      algebraicPolynomialODE_rescale hdiff hode hb, v5_broad_arithmetic_rescale131 ha b⟩
    exact hdiff.comp ((differentiable_const (b : ℂ)).mul differentiable_id)

end StrictEUnit
#print axioms StrictEUnit.v5_broad_arithmetic_rescale131
#print axioms StrictEUnit.v5_broad_function_rescale131
