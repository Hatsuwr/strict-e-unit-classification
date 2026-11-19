import FiniteDiagonalBinomialInverse

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

/-- A genuinely SHARED exponential bounded-log normalizer for the diagonal
order=target-shift family. It covers mixed classes and repeated factors, but
still requires the actual pivot to be nonzero. No unfiltered solution bound
is smuggled into the assumptions. -/
theorem fallingComposite_diagonal_shared_log_normalization
    {ι : Type*} [Fintype ι] (rho : ι → K)
    (hrho : JointBinomialPrefixDenominators rho) (q d : ℕ) :
    ∃ B : ℝ,1≤B ∧ ∀ N : ℕ,∃ e : ℕ,0<e ∧ (e : ℝ)≤B^(N+1) ∧
      ∀ (u : Fin q → ι) v n,n≤N →
        (fallingCompositeSymbol rho u (fun _ => n)).eval (rho v+(n : K))≠0 →
        ∀ (Z : K) (f : Polynomial K),f.natDegree≤d →
          (∀ j,IsIntegral ℤ (Z*(shiftedPolynomialDifferentialOperator (rho v+(n : K))
            (fallingCompositeSymbol rho u (fun _ => n)) f).coeff j)) →
          ∀ j,IsIntegral ℤ ((e : K)*Z*f.coeff j) := by
  obtain ⟨H,hH,hden⟩ := jointBinomialPrefixDenominators_sub rho hrho
  obtain ⟨C,hC,hinv⟩ := fallingComposite_diagonal_shared_inverse rho hrho q
  have hA : 1≤H^q*(16 : ℝ)^d := one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ hH) (one_le_pow₀ (by norm_num))
  refine ⟨(H^q*16^d*C)^(d+1),one_le_pow₀ (one_le_mul_of_one_le_of_one_le hA hC),?_⟩
  intro N
  obtain ⟨D,hD,hDb,hDi⟩ := hden N
  obtain ⟨b,hb,hbb,hbi⟩ := hinv N
  let a := D^q*logJetLCM N^d
  have ha : 0<a := mul_pos (pow_pos hD _) (pow_pos (logJetLCM_pos N) _)
  have hab : (a : ℝ)≤(H^q*16^d)^(N+1) := by
    have hd : (D : ℝ)^q≤(H^q)^(N+1) := by
      rw [pow_right_comm]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hDb q
    have hl : (logJetLCM N : ℝ)^d≤((16 : ℝ)^d)^(N+1) := by
      rw [pow_right_comm]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _)
        ((logJetLCM_real_le_sixteen_pow N).trans (pow_le_pow_right₀ (by norm_num) (Nat.le_succ _))) d
    simp only [a,Nat.cast_mul,Nat.cast_pow,mul_pow]
    exact mul_le_mul hd hl (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (pow_nonneg (le_trans zero_le_one hH) _) _)
  refine ⟨(a*b)^(d+1),pow_pos (mul_pos ha hb) _,?_,?_⟩
  · rw [Nat.cast_pow,Nat.cast_mul,pow_right_comm]
    apply pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    rw [mul_pow]
    exact mul_le_mul hab hbb (Nat.cast_nonneg _) (pow_nonneg (le_trans zero_le_one hA) _)
  · intro u v n hn hp Z f hf hforced j
    have hjet := fallingCompositeSymbol_logJet_common rho u (fun _ => n) v D N n d
      (fun _ => hn) (by intro k hk w;rw [field_choose_eq_descPochhammer_div];exact hDi k hk (v,w))
    exact shiftedPolynomialDifferentialEquation_integer_normalization _ f _ Z a b d ha hp hf
      hjet (hbi u v n hn hp) hforced j

end StrictEUnit
end
