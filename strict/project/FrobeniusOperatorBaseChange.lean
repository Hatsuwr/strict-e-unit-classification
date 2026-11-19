import FrobeniusIntegerLiteralBasis

/-! Exact base change of the explicit logarithmic right inverse. This is an
arithmetic descent ingredient, with no denominator or conjugate-growth claim. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K L : Type*} [Field K] [Field L] (φ : K →+* L)

theorem polynomialMap_smul (c : K) (p : Polynomial K) :
    (c • p).map φ = φ c • p.map φ := by
  simp only [Polynomial.smul_eq_C_mul,Polynomial.map_mul,Polynomial.map_C]

theorem polynomialDifferentialOperator_map (P p : Polynomial K) :
    (polynomialDifferentialOperator P p).map φ =
      polynomialDifferentialOperator (P.map φ) (p.map φ) := by
  simp only [polynomialDifferentialOperator_apply,Polynomial.map_sum,
    Polynomial.support_map_of_injective P φ.injective,Polynomial.coeff_map,
    polynomialMap_smul,Polynomial.iterate_derivative_map]

theorem polynomialDifferentialOperatorInverseAux_map (P : Polynomial K) (n : ℕ)
    (p : Polynomial K) :
    (polynomialDifferentialOperatorInverseAux P n p).map φ =
      polynomialDifferentialOperatorInverseAux (P.map φ) n (p.map φ) := by
  have hdiv : P.divX.map φ = (P.map φ).divX := by
    ext j
    simp only [Polynomial.coeff_map,Polynomial.coeff_divX]
  induction n generalizing p with
  | zero => simp only [polynomialDifferentialOperatorInverseAux,Polynomial.map_zero]
  | succ n ih =>
    simp only [polynomialDifferentialOperatorInverseAux,polynomialMap_smul,
      Polynomial.map_sub,polynomialDifferentialOperator_map,ih,hdiv,
      Polynomial.derivative_map,Polynomial.coeff_map,map_inv₀]

theorem polynomialDifferentialOperatorInverse_map (P p : Polynomial K) :
    (polynomialDifferentialOperatorInverse P p).map φ =
      polynomialDifferentialOperatorInverse (P.map φ) (p.map φ) := by
  simp only [polynomialDifferentialOperatorInverse,polynomialDifferentialOperatorInverseAux_map,
    Polynomial.natDegree_map_eq_of_injective φ.injective]

theorem polynomialPrimitive_map (p : Polynomial K) :
    (polynomialPrimitive p).map φ = polynomialPrimitive (p.map φ) := by
  simp only [polynomialPrimitive,Polynomial.sum_def,Polynomial.map_sum,
    Polynomial.support_map_of_injective p φ.injective,Polynomial.map_monomial,
    Polynomial.coeff_map,map_div₀,map_add,map_natCast,map_one]

variable [CharZero K] [CharZero L]

theorem polynomialIteratedPrimitive_map (q : ℕ) (p : Polynomial K) :
    (polynomialIteratedPrimitive q p).map φ = polynomialIteratedPrimitive q (p.map φ) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    change (polynomialPrimitive^[q+1] p).map φ = polynomialPrimitive^[q+1] (p.map φ)
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply',polynomialPrimitive_map]
    exact congrArg polynomialPrimitive ih

theorem shiftedPolynomialDifferentialRightInverse_map (c : K) (P p : Polynomial K) :
    (shiftedPolynomialDifferentialRightInverse c P p).map φ =
      shiftedPolynomialDifferentialRightInverse (φ c) (P.map φ) (p.map φ) := by
  have hq := Polynomial.eq_rootMultiplicity_map (p := P) φ.injective c
  have hr : (polynomialDifferentialResidualShift c P).map φ =
      polynomialDifferentialResidualShift (φ c) (P.map φ) := by
    simp only [polynomialDifferentialResidualShift,polynomialDifferentialResidual,
      Polynomial.map_comp,Polynomial.map_divByMonic φ ((Polynomial.monic_X_sub_C c).pow _),
      Polynomial.map_pow,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,
      Polynomial.map_add,hq]
  simp only [shiftedPolynomialDifferentialRightInverse,polynomialIteratedPrimitive_map,
    polynomialDifferentialOperatorInverse_map,hr,hq]

end StrictEUnit
end

#print axioms StrictEUnit.polynomialMap_smul
#print axioms StrictEUnit.polynomialDifferentialOperator_map
#print axioms StrictEUnit.polynomialDifferentialOperatorInverseAux_map
#print axioms StrictEUnit.polynomialDifferentialOperatorInverse_map
#print axioms StrictEUnit.polynomialPrimitive_map
#print axioms StrictEUnit.polynomialIteratedPrimitive_map
#print axioms StrictEUnit.shiftedPolynomialDifferentialRightInverse_map
