import FrobeniusDifferentialInverseBound

/-! Bounds for the literal differential forcing operators and their composition
with the canonical inverse, including the factorial-normalization degree gap. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit

theorem polynomialLogSize_shiftedDerivative_iterate_le (d : ℕ) (c : ℂ)
    (M : ℝ) (hM : ((d : ℝ)+1)^2+‖c‖ ≤ M) (f : Polynomial ℂ)
    (hf : f.natDegree ≤ d) (i : ℕ) :
    polynomialLogSize d ((shiftedPolynomialDerivative c)^[i] f) ≤ M^i*polynomialLogSize d f := by
  have hM0 : 0 ≤ M := (add_nonneg (sq_nonneg _) (norm_nonneg _)).trans hM
  have hdeg (j : ℕ) : ((shiftedPolynomialDerivative c)^[j] f).natDegree ≤ d := by
    induction j with
    | zero => exact hf
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact (shiftedPolynomialDerivative_natDegree_le _ _).trans ih
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply',pow_succ]
    calc
      _ ≤ (((d : ℝ)+1)^2+‖c‖)*polynomialLogSize d ((shiftedPolynomialDerivative c)^[i] f) :=
        polynomialLogSize_shiftedDerivative_le _ _ _ (hdeg i)
      _ ≤ M*(M^i*polynomialLogSize d f) :=
        mul_le_mul hM ih (polynomialLogSize_nonneg d _) hM0
      _ = _ := by ring

/-- Derived polynomial growth for a full shifted differential operator. -/
theorem complexPolynomial_differential_upper (Q : Polynomial ℂ) (rho : ℂ) (d q : ℕ)
    (hdeg : Q.natDegree ≤ q) :
    ∃ C : ℝ,0<C ∧ ∀ n : ℕ,∀ f : Polynomial ℂ,f.natDegree≤d →
      polynomialLogSize d (shiftedPolynomialDifferentialOperator (rho+(n : ℂ)) Q f) ≤
        C*((n : ℝ)+1)^q*polynomialLogSize d f := by
  let S : ℝ := ∑ i ∈ Q.support,‖Q.coeff i‖
  let M : ℝ := ((d : ℝ)+1)^2+‖rho‖+1
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hM : 1 ≤ M := by dsimp [M]; nlinarith [norm_nonneg rho,sq_nonneg ((d : ℝ)+1)]
  refine ⟨S*M^q+1,by positivity,?_⟩
  intro n f hf
  let x : ℝ := (n : ℝ)+1
  have hx : 1 ≤ x := by dsimp [x]; linarith [show 0 ≤ (n : ℝ) from Nat.cast_nonneg n]
  have hMx : 1 ≤ M*x := one_le_mul_of_one_le_of_one_le hM hx
  have hr : ((d : ℝ)+1)^2+‖rho+(n : ℂ)‖ ≤ M*x := by
    have ht := norm_add_le rho (n : ℂ)
    rw [Complex.norm_natCast] at ht
    dsimp [M,x]
    nlinarith [norm_nonneg rho,show 0 ≤ (n : ℝ) from Nat.cast_nonneg n,sq_nonneg ((d : ℝ)+1)]
  have he : shiftedPolynomialDifferentialOperator (rho+(n : ℂ)) Q f =
      ∑ i ∈ Q.support,Q.coeff i • (shiftedPolynomialDerivative (rho+(n : ℂ)))^[i] f := by
    rw [shiftedPolynomialDifferentialOperator,Polynomial.aeval_endomorphism,Polynomial.sum_def]
    simp only [Module.End.pow_apply]
  rw [he]
  calc
    _ ≤ ∑ i ∈ Q.support,polynomialLogSize d (Q.coeff i • (shiftedPolynomialDerivative (rho+(n : ℂ)))^[i] f) :=
      polynomialLogSize_sum_le d Q.support _
    _ ≤ ∑ i ∈ Q.support,‖Q.coeff i‖*((M*x)^q*polynomialLogSize d f) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [polynomialLogSize_smul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (polynomialLogSize_shiftedDerivative_iterate_le d _ (M*x) hr f hf i).trans
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hMx
          ((Polynomial.le_natDegree_of_mem_supp i hi).trans hdeg)) (polynomialLogSize_nonneg d f))
    _ = (S*M^q)*x^q*polynomialLogSize d f := by rw [← Finset.sum_mul,mul_pow]; ring
    _ ≤ (S*M^q+1)*x^q*polynomialLogSize d f := by
      apply mul_le_mul_of_nonneg_right _ (polynomialLogSize_nonneg d f)
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- Full inverse-times-forcing estimate, not a scalar surrogate. -/
theorem complexPolynomial_eventually_differential_factorial_ratio_bound
    (P Q : Polynomial ℂ) (hP : P ≠ 0) (rho eta : ℂ) (d k : ℕ)
    (hk : k ≤ P.natDegree) (hQ : Q.natDegree ≤ P.natDegree-k) :
    ∃ N : ℕ,∃ C : ℝ,0<C ∧ ∀ n : ℕ,N≤n → ∀ f : Polynomial ℂ,f.natDegree≤d →
      (n.descFactorial k : ℝ)*polynomialLogSize d
        (shiftedPolynomialDifferentialRightInverse (rho+(n : ℂ)) P
          (shiftedPolynomialDifferentialOperator (eta+(n : ℂ)) Q f)) ≤
        C*polynomialLogSize d f := by
  obtain ⟨N,Cp,hCp,hp⟩ := complexPolynomial_eventually_differential_inverse_bound P hP rho d
  obtain ⟨Cq,hCq,hq⟩ := complexPolynomial_differential_upper Q eta d (P.natDegree-k) hQ
  refine ⟨N,Cp*Cq,mul_pos hCp hCq,?_⟩
  intro n hn f hf
  let x : ℝ := (n : ℝ)+1
  have hx : 0<x := by dsimp [x]; positivity
  have hfd : (shiftedPolynomialDifferentialOperator (eta+(n : ℂ)) Q f).natDegree ≤ d :=
    (shiftedPolynomialDifferentialOperator_natDegree_le _ _ _).trans hf
  have hi := (hp n hn).2 _ hfd
  have hu := hq n f hf
  have hb : polynomialLogSize d (shiftedPolynomialDifferentialRightInverse (rho+(n : ℂ)) P
      (shiftedPolynomialDifferentialOperator (eta+(n : ℂ)) Q f)) ≤
      (Cp/x^P.natDegree)*(Cq*x^(P.natDegree-k)*polynomialLogSize d f) :=
    hi.trans (mul_le_mul_of_nonneg_left hu (by positivity))
  have hfact : (n.descFactorial k : ℝ) ≤ x^k := by
    have h : (n.descFactorial k : ℝ) ≤ (n : ℝ)^k := by exact_mod_cast n.descFactorial_le_pow k
    exact h.trans (pow_le_pow_left₀ (Nat.cast_nonneg n) (by dsimp [x]; linarith) k)
  calc
    _ ≤ x^k*((Cp/x^P.natDegree)*(Cq*x^(P.natDegree-k)*polynomialLogSize d f)) :=
      mul_le_mul hfact hb (polynomialLogSize_nonneg d _) (by positivity)
    _ = (Cp*Cq)*polynomialLogSize d f := by
      have hd : x^k*x^(P.natDegree-k) = x^P.natDegree := by rw [← pow_add,Nat.add_sub_of_le hk]
      calc
        _ = (Cp*Cq*polynomialLogSize d f)*(x^k*x^(P.natDegree-k))/x^P.natDegree := by ring
        _ = _ := by rw [hd]; exact mul_div_cancel_right₀ _ (pow_ne_zero _ (ne_of_gt hx))

end StrictEUnit
end
