import FrobeniusIndicialLargeIndexBound

/-! Polynomial upper bounds and factorial-weighted SCALAR symbol ratios.
These estimates do not silently replace the logarithmic differential operator
by its scalar diagonal. The off-diagonal inverse estimates remain separate. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit

theorem complexPolynomial_eval_upper (Q : Polynomial ℂ) (rho : ℂ) (d : ℕ)
    (hdeg : Q.natDegree ≤ d) :
    ∃ C : ℝ,0<C ∧ ∀ n : ℕ,‖Q.eval (rho+(n : ℂ))‖ ≤ C*((n : ℝ)+1)^d := by
  let S : ℝ := ∑ i ∈ Q.support,‖Q.coeff i‖
  let M : ℝ := ‖rho‖+1
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i hi => norm_nonneg _)
  have hM : 1 ≤ M := by dsimp [M]; linarith [norm_nonneg rho]
  refine ⟨S*M^d+1,by positivity,?_⟩
  intro n
  let x : ℝ := (n : ℝ)+1
  have hx : 1 ≤ x := by dsimp [x]; linarith [show 0 ≤ (n : ℝ) from Nat.cast_nonneg n]
  have hMx : 1 ≤ M*x := one_le_mul_of_one_le_of_one_le hM hx
  have hr : ‖rho+(n : ℂ)‖ ≤ M*x := by
    have ht := norm_add_le rho (n : ℂ)
    rw [Complex.norm_natCast] at ht
    dsimp [M,x]
    nlinarith [norm_nonneg rho,show 0 ≤ (n : ℝ) from Nat.cast_nonneg n]
  have he : ‖Q.eval (rho+(n : ℂ))‖ ≤ S*(M*x)^d := by
    rw [Polynomial.eval_eq_sum]
    calc
      _ ≤ ∑ i ∈ Q.support,‖Q.coeff i * (rho+(n : ℂ))^i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Q.support,‖Q.coeff i‖*(M*x)^d := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul,norm_pow]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact (pow_le_pow_left₀ (norm_nonneg _) hr i).trans
          (pow_le_pow_right₀ hMx ((Polynomial.le_natDegree_of_mem_supp i hi).trans hdeg))
      _ = S*(M*x)^d := (Finset.sum_mul _ _ _).symm
  calc
    _ ≤ S*(M*x)^d := he
    _ = (S*M^d)*x^d := by rw [mul_pow]; ring
    _ ≤ (S*M^d+1)*x^d := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- The correct degree gap cancels the factorial-normalization power for
SCALAR diagonal symbols. Constants are proved, not supplied. -/
theorem complexPolynomial_eventually_weighted_ratio_bound
    (P Q : Polynomial ℂ) (hP : P ≠ 0) (rho eta : ℂ) (k : ℕ)
    (hk : k ≤ P.natDegree) (hQ : Q.natDegree ≤ P.natDegree-k) :
    ∃ N : ℕ,∃ C : ℝ,0<C ∧ ∀ n : ℕ,N≤n →
      ‖(P.eval (rho+(n : ℂ)))⁻¹‖ * ‖Q.eval (eta+(n : ℂ))‖ * ((n : ℝ)+1)^k ≤ C := by
  obtain ⟨N,Cp,hCp,hp⟩ := complexPolynomial_eventually_inverse_bound P hP rho
  obtain ⟨Cq,hCq,hq⟩ := complexPolynomial_eval_upper Q eta (P.natDegree-k) hQ
  refine ⟨N,Cp*Cq,mul_pos hCp hCq,?_⟩
  intro n hn
  let x : ℝ := (n : ℝ)+1
  have hx : 0<x := by dsimp [x]; positivity
  have hmul := mul_le_mul (hp n hn).2 (hq n) (norm_nonneg _) (by positivity)
  have he : (Cp/x^P.natDegree)*(Cq*x^(P.natDegree-k))*x^k = Cp*Cq := by
    have hd : x^(P.natDegree-k)*x^k = x^P.natDegree := by rw [← pow_add,Nat.sub_add_cancel hk]
    calc
      _ = (Cp*Cq)*(x^(P.natDegree-k)*x^k)/x^P.natDegree := by ring
      _ = Cp*Cq := by rw [hd]; exact mul_div_cancel_right₀ _ (pow_ne_zero _ (ne_of_gt hx))
  exact (mul_le_mul_of_nonneg_right hmul (pow_nonneg (le_of_lt hx) k)).trans_eq he

/-- Falling factorials are the literal factorial ratios appearing after
normalization. This bound still concerns scalar symbols only. -/
theorem complexPolynomial_eventually_factorial_ratio_bound
    (P Q : Polynomial ℂ) (hP : P ≠ 0) (rho eta : ℂ) (k : ℕ)
    (hk : k ≤ P.natDegree) (hQ : Q.natDegree ≤ P.natDegree-k) :
    ∃ N : ℕ,∃ C : ℝ,0<C ∧ ∀ n : ℕ,N≤n →
      ‖(P.eval (rho+(n : ℂ)))⁻¹‖ * ‖Q.eval (eta+(n : ℂ))‖ * (n.descFactorial k : ℝ) ≤ C := by
  obtain ⟨N,C,hC,hbound⟩ := complexPolynomial_eventually_weighted_ratio_bound P Q hP rho eta k hk hQ
  refine ⟨N,C,hC,?_⟩
  intro n hn
  have hf : (n.descFactorial k : ℝ) ≤ ((n : ℝ)+1)^k := by
    have h : (n.descFactorial k : ℝ) ≤ (n : ℝ)^k := by exact_mod_cast n.descFactorial_le_pow k
    exact h.trans (pow_le_pow_left₀ (Nat.cast_nonneg n) (by linarith) k)
  exact (mul_le_mul_of_nonneg_left hf (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans (hbound n hn)

end StrictEUnit
end

#print axioms StrictEUnit.complexPolynomial_eval_upper
#print axioms StrictEUnit.complexPolynomial_eventually_weighted_ratio_bound
#print axioms StrictEUnit.complexPolynomial_eventually_factorial_ratio_bound
