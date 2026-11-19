import EulerShiftedConnectionArithmetic
import PolynomialDifferentialOperator

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem normalizedFallingSymbol_ne_zero (m : ℕ) :
    normalizedFallingSymbol (K:=K) m≠0 := by
  apply mul_ne_zero
  · exact Polynomial.C_ne_zero.mpr (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)))
  · exact (monic_descPochhammer K m).ne_zero

/-- With log degree at most q, the (q+1)-st power is necessary: one simple
binomial zero alone does not annihilate a logarithmic coefficient. -/
theorem frobenius_falling_log_filter_low_index (m n q : ℕ) (hn : n<m)
    (f : Polynomial K) (hf : f.natDegree≤q) :
    shiftedPolynomialDifferentialOperator (n : K)
      ((normalizedFallingSymbol (K:=K) m)^(q+1)) f=0 := by
  have hP := pow_ne_zero (q+1) (normalizedFallingSymbol_ne_zero (K:=K) m)
  apply (shiftedPolynomialDifferentialOperator_kernel_iff _ _ _ hP).2
  have hz : (normalizedFallingSymbol (K:=K) m).IsRoot (n : K) := by
    rw [Polynomial.IsRoot,normalizedFallingSymbol_eval,Ring.choose_natCast,Nat.choose_eq_zero_of_lt hn,Nat.cast_zero]
  have hd : (Polynomial.X-Polynomial.C (n : K))^(q+1)∣(normalizedFallingSymbol (K:=K) m)^(q+1) :=
    pow_dvd_pow_of_dvd (Polynomial.dvd_iff_isRoot.mpr hz) (q+1)
  have hm := (Polynomial.le_rootMultiplicity_iff hP).2 hd
  exact lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le hf)
    (by exact_mod_cast (show q<(((normalizedFallingSymbol (K:=K) m)^(q+1)).rootMultiplicity (n : K)) by omega))

/-- At the retained diagonal index the filter is nonresonant, even for logs.
This is an exact invertibility statement, not an arithmetic inverse bound. -/
theorem frobenius_falling_log_filter_diagonal_bijective (m q : ℕ) :
    Function.Bijective (shiftedPolynomialDifferentialOperator (m : K)
      ((normalizedFallingSymbol (K:=K) m)^(q+1))) := by
  have hP := pow_ne_zero (q+1) (normalizedFallingSymbol_ne_zero (K:=K) m)
  have he : (((normalizedFallingSymbol (K:=K) m)^(q+1)).comp
      (Polynomial.X+Polynomial.C (m : K))).coeff 0=1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero,Polynomial.eval_comp,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_C,zero_add,Polynomial.eval_pow,
      normalizedFallingSymbol_eval,Ring.choose_natCast,Nat.choose_self,Nat.cast_one,one_pow]
  refine ⟨?_,shiftedPolynomialDifferentialOperator_surjective _ _ hP⟩
  rw [shiftedPolynomialDifferentialOperator_eq]
  exact polynomialDifferentialOperator_injective _ (he.trans_ne one_ne_zero)

end StrictEUnit
end
