import LogMixingFallingInverse

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

theorem normalizedFallingSymbol_noninteger_pivot (rho : K)
    (h : ∀ n : ℕ,rho+(n+1:ℕ)≠0) (n : ℕ) :
    (normalizedFallingSymbol (K:=K) n).eval (rho+(n:K))≠0 := by
  have hp (m : ℕ) : (descPochhammer K m).eval (rho+(m:K))≠0 := by
    induction m with
    | zero => simp
    | succ m ih =>
      have he := congrArg (fun P : Polynomial K =>P.eval 0) (shifted_descPochhammer_rising_succ rho m)
      simp only [Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,
        zero_add,Polynomial.eval_mul] at he
      rw [he]
      exact mul_ne_zero ih (h m)
  simp only [normalizedFallingSymbol,Polynomial.eval_mul,Polynomial.eval_C]
  exact mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))) (hp n)

theorem jointBinomialPrefixDenominators_adjoin_zero {ι : Type*} [Fintype ι]
    (rho : ι →K) (hrho : JointBinomialPrefixDenominators rho) :
    JointBinomialPrefixDenominators (fun i : Option ι =>i.elim 0 rho) := by
  apply finite_binomialPrefixDenominators
  intro i
  cases i with
  | none =>
    refine ⟨1,by norm_num,fun N =>⟨1,by omega,by simp,?_⟩⟩
    intro m hm
    rw [← field_choose_eq_descPochhammer_div]
    simp only [Option.elim_none,Nat.cast_one,one_mul]
    simpa using (resonance_integer_choose_integral (K:=K) 0 m)
  | some i =>
    obtain ⟨C,hC,hden⟩ := hrho
    refine ⟨C,hC,fun N =>?_⟩
    obtain ⟨D,hD,hDb,hDi⟩ := hden N
    exact ⟨D,hD,hDb,fun m hm =>hDi m hm i⟩

/-- The complete finite-log normalized mixing matrix has a SHARED exponential
prefix denominator, derived from exponent-binomial arithmetic. C is a conclusion. -/
theorem factorialLogMixing_shared_matrix_bound {ι : Type*} [Fintype ι]
    (rho : ι →K) (hrho : JointBinomialPrefixDenominators rho) (d : ℕ) :
    ∃ C : ℝ,1≤C ∧ ∀ N : ℕ,∃ Q : ℕ,0<Q ∧ (Q:ℝ)≤C^(N+1) ∧
      ∀ i,(∀ m : ℕ,rho i+(m+1:ℕ)≠0) →∀ n,n≤N →∀ j,j≤d →∀ t,
        IsIntegral ℤ ((Q:K)*(factorialLogMixing (rho i) n (Polynomial.X^j)).coeff t) := by
  let r : Option ι →K :=fun i =>i.elim 0 rho
  have hr := jointBinomialPrefixDenominators_adjoin_zero rho hrho
  obtain ⟨C,hC,hden⟩ := fallingComposite_diagonal_shared_log_normalization r hr 1 d
  refine ⟨C,hC,fun N =>?_⟩
  obtain ⟨Q,hQ,hQb,hQi⟩ := hden N
  refine ⟨Q,hQ,hQb,?_⟩
  intro i hi n hn j hj t
  have he : fallingCompositeSymbol r (fun _ : Fin 1 =>none) (fun _ =>n)=normalizedFallingSymbol n := by
    simp [fallingCompositeSymbol,r]
  have hd : (factorialLogMixing (rho i) n (Polynomial.X^j)).natDegree≤d :=
    (Polynomial.natDegree_smul_le _ _).trans
      ((logMixingForward_natDegree_le _ _ _).trans (by simpa using hj))
  have hforced : ∀ k,IsIntegral ℤ ((1:K)*
      (shiftedPolynomialDifferentialOperator (r (some i)+(n:K))
        (fallingCompositeSymbol r (fun _ : Fin 1 =>none) (fun _ =>n))
        (factorialLogMixing (rho i) n (Polynomial.X^j))).coeff k) := by
    intro k
    rw [he]
    change IsIntegral ℤ (1*(shiftedPolynomialDifferentialOperator (rho i+(n:K)) _ _).coeff k)
    rw [factorialLogMixing_falling_inverse (rho i) hi,one_mul]
    simp only [Polynomial.coeff_X_pow]
    split_ifs <;> first | exact isIntegral_one | exact isIntegral_zero
  have hh := hQi (fun _ : Fin 1 =>none) (some i) n hn
    (by rw [he];exact normalizedFallingSymbol_noninteger_pivot (rho i) hi n)
    1 (factorialLogMixing (rho i) n (Polynomial.X^j)) hd hforced t
  simpa only [mul_one] using hh
end StrictEUnit
end
