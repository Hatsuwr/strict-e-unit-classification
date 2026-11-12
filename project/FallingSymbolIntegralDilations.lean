import BoundedLogNormalizationJet

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem descPochhammer_eval_shifted_product (m : ℕ) (x : K) :
    (descPochhammer K (m+1)).eval x=x*∏ j ∈ Finset.range m,(x-((j+1 : ℕ) : K)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [descPochhammer_succ_eval,ih,Finset.prod_range_succ]
    ring

/-- The normalized falling polynomial has only reciprocals of integers up to
m+1 in its factored form. This is an identity, not a coefficient bound. -/
theorem normalizedFallingSymbol_factorization (m : ℕ) :
    normalizedFallingSymbol (K:=K) (m+1)=
      (Polynomial.C (((m+1 : ℕ) : K)⁻¹)*Polynomial.X)*
        ∏ j ∈ Finset.range m,(Polynomial.C (((j+1 : ℕ) : K)⁻¹)*Polynomial.X-1) := by
  apply Polynomial.funext
  intro x
  simp only [normalizedFallingSymbol,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_one,
    descPochhammer_eval_shifted_product]
  have hdiv (j : ℕ) : (((j+1 : ℕ) : K)⁻¹*x-1)=(x-((j+1 : ℕ) : K))/((j+1 : ℕ) : K) := by
    have hj : (j : K)+1≠0 := by exact_mod_cast Nat.succ_ne_zero j
    push_cast
    field_simp
  simp_rw [hdiv]
  rw [Finset.prod_div_distrib,← Nat.cast_prod,Finset.prod_range_add_one_eq_factorial,
    Nat.factorial_succ,Nat.cast_mul]
  simp only [mul_inv_rev,div_eq_mul_inv]
  ring

theorem integral_nat_quotient_of_dvd (L m : ℕ) (hm : 0<m) (h : m∣L) :
    IsIntegral ℤ ((L : K)/(m : K)) := by
  obtain ⟨k,rfl⟩ := h
  have he : ((m*k : ℕ) : K)/(m : K)=(k : K) := by
    push_cast
    field_simp [Nat.cast_ne_zero.mpr (ne_of_gt hm)]
  rw [he]
  exact ordinaryJet_natCast_integral k


theorem polynomial_integral_coeff_mul (P Q : Polynomial K)
    (hP : ∀ j,IsIntegral ℤ (P.coeff j)) (hQ : ∀ j,IsIntegral ℤ (Q.coeff j)) :
    ∀ j,IsIntegral ℤ ((P*Q).coeff j) := by
  intro j
  rw [Polynomial.coeff_mul]
  exact IsIntegral.sum _ (fun ab _ => (hP ab.1).mul (hQ ab.2))

theorem polynomial_integral_coeff_prod {ι : Type*} (s : Finset ι) (P : ι → Polynomial K)
    (hP : ∀ i∈s,∀ j,IsIntegral ℤ ((P i).coeff j)) :
    ∀ j,IsIntegral ℤ ((∏ i∈s,P i).coeff j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro j
    simp only [Finset.prod_empty,Polynomial.coeff_one]
    split_ifs <;> first | exact isIntegral_one | exact isIntegral_zero
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact polynomial_integral_coeff_mul _ _ (hP i (Finset.mem_insert_self _ _))
      (ih (fun k hk => hP k (Finset.mem_insert_of_mem hk)))

/-- Divisibility by 1,...,N, not N!, is enough: F_m(L*X) is integral. -/
theorem normalizedFallingSymbol_integral_dilation (L N m : ℕ) (hm : m≤N)
    (hL : ∀ k,0<k → k≤N → k∣L) :
    ∀ j,IsIntegral ℤ (((normalizedFallingSymbol (K:=K) m).comp
      (Polynomial.C (L : K)*Polynomial.X)).coeff j) := by
  classical
  cases m with
  | zero =>
    intro j
    simp only [normalizedFallingSymbol,Nat.factorial_zero,Nat.cast_one,inv_one,
      Polynomial.C_1,descPochhammer_zero,mul_one,Polynomial.one_comp,Polynomial.coeff_one]
    split_ifs <;> first | exact isIntegral_one | exact isIntegral_zero
  | succ m =>
    rw [normalizedFallingSymbol_factorization,Polynomial.mul_comp,Polynomial.prod_comp]
    have factor (k : ℕ) (hk : 0<k) (hkN : k≤N) :
        ∀ j,IsIntegral ℤ (((Polynomial.C ((k : K)⁻¹)*Polynomial.X).comp
          (Polynomial.C (L : K)*Polynomial.X)).coeff j) := by
      intro j
      rw [Polynomial.mul_comp,Polynomial.C_comp,Polynomial.X_comp,← mul_assoc,← Polynomial.C_mul]
      simp only [Polynomial.coeff_C_mul,Polynomial.coeff_X]
      split_ifs
      · simp only [mul_one]
        simpa only [div_eq_mul_inv,mul_comm] using integral_nat_quotient_of_dvd (K:=K) L k hk (hL k hk hkN)
      · simpa only [mul_zero] using (isIntegral_zero : IsIntegral ℤ (0 : K))
    apply polynomial_integral_coeff_mul _ _ (factor (m+1) (by omega) hm)
    apply polynomial_integral_coeff_prod
    intro k hk
    rw [Polynomial.sub_comp,Polynomial.one_comp]
    apply polynomial_subring_sub (integralClosure ℤ K).toSubring _ _
      (factor (k+1) (by omega) (by have := Finset.mem_range.mp hk;omega))
    intro j
    simp only [Polynomial.coeff_one]
    split_ifs <;> first | exact isIntegral_one | exact isIntegral_zero

end StrictEUnit
end
