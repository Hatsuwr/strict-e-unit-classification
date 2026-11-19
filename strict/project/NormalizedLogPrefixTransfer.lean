import FiniteLogMixingDenominatorTransfer

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

/-- Conditional full-log prefix transfer. The finite-degree normalized mixing
matrix estimate is an explicit remaining hypothesis, not inferred here. -/
theorem normalizedLogLaplace_prefix_transfer
    (rho : K) (h : ∀ n : ℕ,rho+(n+1:ℕ)≠0)
    (u : LaurentSeries (Polynomial K)) (d : ℕ)
    (hd : ∀ n : ℕ,(u.coeff ((n:ℤ)+1)).natDegree≤d)
    (hu : LogSeriesPrefixArithmetic u)
    (hmix : ∃ C : ℝ,1≤C ∧ ∀ N : ℕ,∃ Q : ℕ,0<Q ∧ (Q:ℝ)≤C^(N+1) ∧
      ∀ n,n≤N →∀ j,j≤d →∀ t,
        IsIntegral ℤ ((Q:K)*(factorialLogMixing rho n (Polynomial.X^j)).coeff t)) :
    ∃ A : ℝ,1≤A ∧ ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D:ℝ)≤A^(N+1) ∧
      ∀ n,n≤N →∀ t,IsIntegral ℤ ((D:K)*(n.factorial:K)*
        ((generalizedLogLaplaceSeries rho h u).coeff (n:ℤ)).coeff t) := by
  obtain ⟨B,hB,hden⟩ := hu
  obtain ⟨C,hC,hmix⟩ := hmix
  refine ⟨B^2*C,?_,?_⟩
  · nlinarith [sq_nonneg (B-1)]
  intro N
  obtain ⟨D,hD,hDb,hDi⟩ := hden (N+1)
  obtain ⟨Q,hQ,hQb,hQi⟩ := hmix N
  refine ⟨D*Q,Nat.mul_pos hD hQ,?_,?_⟩
  · rw [Nat.cast_mul,mul_pow]
    apply mul_le_mul ?_ hQb (by positivity) (by positivity)
    calc
      (D:ℝ) ≤ B^(N+1+1) := hDb
      _ ≤ B^(2*(N+1)) := pow_le_pow_right₀ hB (by omega)
      _ = (B^2)^(N+1) := pow_mul B 2 (N+1)
  intro n hn t
  have hinput : ∀ j,IsIntegral ℤ ((D:K)*(u.coeff ((n:ℤ)+1)).coeff j) := by
    intro j
    simpa only [Nat.cast_add,Nat.cast_one] using hDi (n+1) (by omega) j
  have hnorm := factorialLogMixing_denominator_transfer rho h n d D Q
    (u.coeff ((n:ℤ)+1)) (hd n) hinput (hQi n hn)
  have he := congrArg (fun p : Polynomial K =>p.coeff t)
    (generalizedLogLaplaceSeries_factorial_log_coefficient rho h u n)
  simp only [Polynomial.coeff_smul,smul_eq_mul] at he
  rw [mul_assoc,he]
  have hi : IsIntegral ℤ ((-1:K)^n) := isIntegral_one.neg.pow n
  convert hi.mul (hnorm t) using 1 <;> ring
end StrictEUnit
end
