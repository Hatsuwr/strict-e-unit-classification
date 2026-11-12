import StrictEFunctionDefinitions
import AlgebraicExponentialDenominators
import Mathlib.Analysis.Polynomial.CauchyBound

/-! The reverse-inclusion building blocks are proved against the full strict
E-function definition, including its number-theoretic conditions. -/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- All complex conjugates of one algebraic number are uniformly bounded,
because each is a root of the same nonzero minimal polynomial. -/
theorem algebraicComplex_conjugates_bounded (α : AlgebraicComplex) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ σ : AlgebraicComplex →ₐ[ℚ] ℂ, ‖σ α‖ ≤ A := by
  let p : Polynomial ℂ := (minpoly ℚ α).map (algebraMap ℚ ℂ)
  have hp : p ≠ 0 := Polynomial.map_ne_zero
    (minpoly.ne_zero (Algebra.IsIntegral.isIntegral α))
  refine ⟨p.cauchyBound, ?_, ?_⟩
  · exact_mod_cast Polynomial.one_le_cauchyBound p
  · intro σ
    have hroot : p.IsRoot (σ α) := by
      change ((minpoly ℚ α).map (algebraMap ℚ ℂ)).eval (σ α) = 0
      rw [Polynomial.eval_map, ← Polynomial.aeval_def, Polynomial.aeval_algHom]
      simp only [AlgHom.comp_apply, minpoly.aeval, map_zero]
    exact_mod_cast (hroot.norm_lt_cauchyBound hp).le

/-- The geometric coefficient sequence of an algebraic scalar exponential
satisfies both the full conjugate and common-denominator conditions. -/
theorem algebraic_scalar_exp_arithmetic (α β : AlgebraicComplex) :
    HasStrictEArithmetic (fun n => α * β ^ n) := by
  obtain ⟨A, hA, hα⟩ := algebraicComplex_conjugates_bounded α
  obtain ⟨B, hB, hβ⟩ := algebraicComplex_conjugates_bounded β
  obtain ⟨D, hD, hd⟩ := algebraic_geometric_common_denominators
    (mem_algebraicClosure_iff.mp α.property) (mem_algebraicClosure_iff.mp β.property)
  let C : ℝ := max (max A B) D
  have hAC : A ≤ C := (le_max_left A B).trans (le_max_left (max A B) D)
  have hBC : B ≤ C := (le_max_right A B).trans (le_max_left (max A B) D)
  have hDC : (D : ℝ) ≤ C := le_max_right _ _
  have hC : 1 ≤ C := hA.trans hAC
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  refine ⟨C, hC, ?_, (fun n => D ^ (n + 1)), ?_, ?_, ?_⟩
  · intro σ n
    simp only [map_mul, map_pow, norm_mul, norm_pow]
    calc
      ‖σ α‖ * ‖σ β‖ ^ n ≤ C * C ^ n :=
        mul_le_mul ((hα σ).trans hAC) (pow_le_pow_left₀ (norm_nonneg _) ((hβ σ).trans hBC) n)
          (pow_nonneg (norm_nonneg _) _) hC0
      _ = C ^ (n + 1) := by rw [pow_succ]; ring
  · intro n
    exact pow_pos hD _
  · intro n
    simpa only [Nat.cast_pow] using pow_le_pow_left₀ (Nat.cast_nonneg D) hDC (n + 1)
  · intro n j hj
    simpa only [map_mul, map_pow] using hd n j hj

/-- The actual factorial-normalized series for α exp(βz). -/
theorem algebraic_scalar_exp_hasSum (α β : AlgebraicComplex) (z : ℂ) :
    HasSum (fun n : ℕ => ((α * β ^ n : AlgebraicComplex) : ℂ) * z ^ n /
      (n.factorial : ℂ)) ((α : ℂ) * Complex.exp ((β : ℂ) * z)) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp ℂ ((β : ℂ) * z)).mul_left (α : ℂ)
  rw [← Complex.exp_eq_exp_ℂ] at h
  convert h using 1
  funext n
  simp only [IntermediateField.coe_mul, IntermediateField.coe_pow, mul_pow]
  ring

/-- This explicit first-order polynomial equation has leading coefficient one. -/
theorem algebraic_scalar_exp_ode (α β : AlgebraicComplex) :
    HasAlgebraicPolynomialODE (fun z : ℂ => (α : ℂ) * Complex.exp ((β : ℂ) * z)) := by
  refine ⟨1, ![Polynomial.C (-β), 1], ?_, ?_⟩
  · refine ⟨1, ?_⟩
    simp
  · intro z
    have hd := (((Complex.hasDerivAt_exp ((β : ℂ) * z)).comp z
      ((hasDerivAt_id z).const_mul (β : ℂ))).const_mul (α : ℂ)).deriv
    simp only [Function.comp_def, mul_one] at hd
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Polynomial.eval₂_C, Polynomial.eval₂_one, Polynomial.eval₂_neg, map_neg, Fin.val_zero, Fin.val_one,
      iteratedDeriv_zero, iteratedDeriv_one, one_mul]
    rw [hd]
    change -(β : ℂ) * ((α : ℂ) * Complex.exp ((β : ℂ) * z)) +
      (α : ℂ) * (Complex.exp ((β : ℂ) * z) * (β : ℂ)) = 0
    ring

/-- Algebraic scalar exponentials genuinely satisfy the complete strict
E-function definition. Neither membership nor arithmetic bounds are assumed. -/
theorem algebraic_scalar_exp_isStrictEFunction (α β : AlgebraicComplex) :
    IsStrictEFunction (fun z : ℂ => (α : ℂ) * Complex.exp ((β : ℂ) * z)) := by
  refine ⟨(fun n => α * β ^ n), ?_, algebraic_scalar_exp_hasSum α β,
    algebraic_scalar_exp_ode α β, algebraic_scalar_exp_arithmetic α β⟩
  exact (differentiable_const (α : ℂ)).mul
    (Complex.differentiable_exp.comp ((differentiable_const (β : ℂ)).mul differentiable_id))

/-- All algebraic constant functions are strict E-functions. -/
theorem algebraic_constant_isStrictEFunction (α : AlgebraicComplex) :
    IsStrictEFunction (fun _ : ℂ => (α : ℂ)) := by
  simpa using algebraic_scalar_exp_isStrictEFunction α 0

/-- Every algebraic number is an actual strict E-value. -/
theorem algebraic_isStrictEValue (α : AlgebraicComplex) : IsStrictEValue (α : ℂ) := by
  exact ⟨_, algebraic_constant_isStrictEFunction α, 0, rfl⟩

/-- Evaluation at one gives the claimed exponential class of strict E-values. -/
theorem algebraic_scalar_exp_isStrictEValue (α β : AlgebraicComplex) :
    IsStrictEValue ((α : ℂ) * Complex.exp (β : ℂ)) := by
  refine ⟨_, algebraic_scalar_exp_isStrictEFunction α β, 1, ?_⟩
  simp

/-- Both the value and its reciprocal are represented by actual strict
E-functions, proving the reverse inclusion without functional-unit assumptions. -/
theorem algebraic_scalar_exp_isStrictEValueUnit (α β : AlgebraicComplex) (hα : α ≠ 0) :
    IsStrictEValueUnit ((α : ℂ) * Complex.exp (β : ℂ)) := by
  have hαC : (α : ℂ) ≠ 0 := by exact_mod_cast hα
  refine ⟨mul_ne_zero hαC (Complex.exp_ne_zero _),
    algebraic_scalar_exp_isStrictEValue α β, ?_⟩
  simpa only [IntermediateField.coe_inv, IntermediateField.coe_neg, Complex.exp_neg, mul_inv_rev, mul_comm] using
    algebraic_scalar_exp_isStrictEValue α⁻¹ (-β)


/-- The constant functions satisfying the strict E-definition are exactly the
algebraic constants, not arbitrary complex constants. -/
theorem constant_isStrictEFunction_iff (c : ℂ) :
    IsStrictEFunction (fun _ : ℂ => c) ↔ IsAlgebraic ℚ c := by
  constructor
  · exact strictEFunction_zero_isAlgebraic
  · intro hc
    exact algebraic_constant_isStrictEFunction ⟨c, mem_algebraicClosure_iff.mpr hc⟩

/-- Reverse inclusion for the numerical class in the manuscript, stated with
ordinary complex algebraic parameters. This is a consequence of the actual
strict E-function construction, not a definition of E-values. -/
theorem algebraic_exponential_reverse_inclusion {u : ℂ}
    (hu : ∃ α β : ℂ, IsAlgebraic ℚ α ∧ α ≠ 0 ∧ IsAlgebraic ℚ β ∧
      u = α * Complex.exp β) : IsStrictEValueUnit u := by
  obtain ⟨α, β, hα, hα0, hβ, rfl⟩ := hu
  exact algebraic_scalar_exp_isStrictEValueUnit
    ⟨α, mem_algebraicClosure_iff.mpr hα⟩ ⟨β, mem_algebraicClosure_iff.mpr hβ⟩
    (fun h => hα0 (congrArg Subtype.val h))

end StrictEUnit
#print axioms StrictEUnit.algebraicComplex_conjugates_bounded
#print axioms StrictEUnit.algebraic_scalar_exp_arithmetic
#print axioms StrictEUnit.algebraic_scalar_exp_hasSum
#print axioms StrictEUnit.algebraic_scalar_exp_ode
#print axioms StrictEUnit.algebraic_scalar_exp_isStrictEFunction
#print axioms StrictEUnit.algebraic_constant_isStrictEFunction
#print axioms StrictEUnit.algebraic_isStrictEValue
#print axioms StrictEUnit.algebraic_scalar_exp_isStrictEValue
#print axioms StrictEUnit.algebraic_scalar_exp_isStrictEValueUnit

#print axioms StrictEUnit.constant_isStrictEFunction_iff
#print axioms StrictEUnit.algebraic_exponential_reverse_inclusion
