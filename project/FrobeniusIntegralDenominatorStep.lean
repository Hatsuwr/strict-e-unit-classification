import FrobeniusUniformIntegralSymbols

/-! A literal denominator propagation step for the existing Frobenius
recurrence. The pivot is b*P(rho+n); no new or easier recurrence is substituted. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem polynomialDifferentialOperator_scaled_shift (b c : K) (P f : Polynomial K) :
    polynomialDifferentialOperator (Polynomial.C b*(P.comp (Polynomial.X+Polynomial.C c))) f =
      b • shiftedPolynomialDifferentialOperator c P f := by
  rw [polynomialDifferentialOperator_mul,← shiftedPolynomialDifferentialOperator_eq]
  simp only [polynomialDifferentialOperator,Polynomial.aeval_C,Module.algebraMap_end_apply]

/-- If D clears the earlier coefficients, the exact scalar pivot to a bounded
power times D clears the next coefficient polynomial. All log coefficients
are cleared at once, including those arising from nontrivial logarithms. -/
theorem polynomialLogFrobeniusCoefficient_integral_denominator_step
    (B : ℕ → Polynomial K) (rho : K) (u0 : Polynomial K) (hP : B 0≠0)
    (b n : ℕ) (hb : 0<b) (hn : n≠0) (hne : (B 0).eval (rho+(n : K))≠0)
    (hclear : ∀ (k s j : ℕ),IsIntegral ℤ ((b : K)*((B k).comp
      (Polynomial.X+Polynomial.C (rho+(s : K)))).coeff j))
    (D : K) (hprev : ∀ s : Fin n,∀ j,IsIntegral ℤ
      (D*(polynomialLogFrobeniusCoefficient B rho u0 s.val).coeff j)) :
    ∀ j,IsIntegral ℤ
      (((b : K)*(B 0).eval (rho+(n : K)))^(u0.natDegree+(B 0).natDegree+1)*
        D*(polynomialLogFrobeniusCoefficient B rho u0 n).coeff j) := by
  let u := polynomialLogFrobeniusCoefficient B rho u0
  let Q (k s : ℕ) := Polynomial.C (b : K)*((B k).comp
    (Polynomial.X+Polynomial.C (rho+(s : K))))
  have hQ (k s j : ℕ) : IsIntegral ℤ ((Q k s).coeff j) := by
    simpa only [Q,Polynomial.coeff_C_mul] using hclear k s j
  have hQ0 : (Q 0 n).coeff 0=(b : K)*(B 0).eval (rho+(n : K)) := by
    simp only [Q,Polynomial.coeff_C_mul,Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.eval_mul,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,zero_add]
  have hnonzero : (Q 0 n).coeff 0≠0 := by
    rw [hQ0]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (ne_of_gt hb)) hne
  have he : polynomialDifferentialOperator (Q 0 n) (D • u n) =
      -(∑ s : Fin n,polynomialDifferentialOperator (Q (n-s.val) s.val) (D • u s.val)) := by
    simp only [Q,polynomialDifferentialOperator_scaled_shift,map_smul,
      polynomialLogFrobeniusCoefficient_recurrence B rho u0 hP n hn,
      polynomialLogLowerSum,smul_neg,Finset.smul_sum,u]
  have hforced : ∀ j,IsIntegral ℤ
      ((polynomialDifferentialOperator (Q 0 n) (D • u n)).coeff j) := by
    rw [he]
    intro j
    rw [Polynomial.coeff_neg]
    apply IsIntegral.neg
    apply polynomial_subring_sum (integralClosure ℤ K).toSubring
    intro s hs
    apply polynomial_subring_differentialOperator (integralClosure ℤ K).toSubring _ _ (hQ _ _)
    intro j
    simpa only [Polynomial.coeff_smul,smul_eq_mul,u] using hprev s j
  have hdegree : (D • u n).natDegree ≤ u0.natDegree+(B 0).natDegree :=
    (Polynomial.natDegree_smul_le _ _).trans (polynomialLogFrobeniusCoefficient_uniform_degree B rho u0 n)
  have h := polynomialDifferentialEquation_integral_pivot_power
    (Q 0 n) (D • u n) (hQ 0 n) hnonzero _ hdegree hforced
  simpa only [hQ0,Polynomial.coeff_smul,smul_eq_mul,mul_assoc,u] using h

end StrictEUnit
end
