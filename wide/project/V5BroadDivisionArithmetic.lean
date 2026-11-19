import V5BroadDivisionCoefficients
import V5BroadDivisionTail

noncomputable section
namespace StrictEUnit

/-- The broad coefficient conditions survive division by 1-X if every
conjugate has zero sum at 1. The original integer denominators are reused.
The vanishing condition is independent and is not inferred by mapping sums. -/
theorem v5_broad_algebraic_division_arithmetic (a : ℕ → AlgebraicComplex)
    (ha : V5BroadAlgebraicArithmetic a)
    (hz : ∀ σ : AlgebraicComplex →ₐ[ℚ] ℂ,
      HasSum (fun n => σ (a n) / (n.factorial : ℂ)) 0) :
    V5BroadAlgebraicArithmetic (v5DivisionCoeff a) := by
  intro ε hε
  let η : ℝ := min ε (1/2)
  have hηpos : 0 < η := lt_min hε (by norm_num)
  have hη : η ≤ 1/2 := min_le_right _ _
  have hηε : η ≤ ε := min_le_left _ _
  obtain ⟨C,hC,d,hd,hdb,hconj,hint⟩ := ha η hηpos
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  obtain ⟨N,hN⟩ := exists_nat_ge ((2*C)^2)
  let M : ℝ := C^(N+1)*(N.factorial : ℝ)^η
  let D := M+(N+1 : ℝ)
  have hfac (n : ℕ) : (1 : ℝ) ≤ (n.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  have hpower (n : ℕ) (e : ℝ) (he : 0 ≤ e) : 1 ≤ (n.factorial : ℝ)^e :=
    Real.one_le_rpow (hfac n) he
  have hCM : C ≤ M := by
    calc
      C ≤ C^(N+1) := by
        simpa only [pow_one] using (pow_le_pow_right₀ hC (show 1 ≤ N+1 by omega))
      _ ≤ M := le_mul_of_one_le_right (by positivity) (hpower N η hηpos.le)
  have hCD : C ≤ D := by
    dsimp [D]
    exact hCM.trans (le_add_of_nonneg_right (by positivity))
  have hD : 1 ≤ D := hC.trans hCD
  have hrpow (n : ℕ) : (n.factorial : ℝ)^η ≤ (n.factorial : ℝ)^ε :=
    Real.rpow_le_rpow_of_exponent_le (hfac n) hηε
  refine ⟨D,hD,d,hd,?_,?_,?_⟩
  · intro n
    exact (hdb n).trans (mul_le_mul (pow_le_pow_left₀ hC0 hCD _) (hrpow n)
      (by positivity) (by positivity))
  · intro σ n
    let b : ℕ → ℂ := fun j => σ (a j)
    have hmap : σ (v5DivisionCoeff a n) = v5DivisionCoeff b n :=
      v5_divisionCoeff_map σ.toRingHom a n
    rw [hmap]
    by_cases hn : N ≤ n
    · have hn' : (2*C)^2 ≤ (n+1 : ℝ) := hN.trans (by exact_mod_cast (show N ≤ n+1 by omega))
      have hb : ‖v5DivisionCoeff b n‖ ≤ C^(n+1)*(n.factorial : ℝ)^η := by
        apply v5_broad_division_tail_norm _ _ _ (v5_divisionCoeff_tail_hasSum b (hz σ) n)
        intro j
        have hk : j+(n+1) = n+j+1 := by omega
        rw [hk, norm_mul, norm_neg, norm_div, Complex.norm_natCast, Complex.norm_natCast]
        calc
          _ ≤ (n.factorial : ℝ) * (C^(n+j+1+1) * ((n+j+1).factorial : ℝ)^η /
              ((n+j+1).factorial : ℝ)) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hconj σ _) (by positivity))
              (by positivity)
          _ = (n.factorial : ℝ) * C^(n+j+1+1) * ((n+j+1).factorial : ℝ)^η /
              ((n+j+1).factorial : ℝ) := by ring
          _ ≤ _ := v5_broad_division_tail_term hC hη n j hn'
      exact hb.trans (mul_le_mul (pow_le_pow_left₀ hC0 hCD _) (hrpow n)
        (by positivity) (by positivity))
    · have hsmall_a (j : ℕ) (hj : j ≤ N) : ‖b j‖ ≤ M := by
        apply (hconj σ j).trans
        apply mul_le_mul (pow_le_pow_right₀ hC (by omega)) _ (by positivity) (by positivity)
        exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.factorial_le hj) hηpos.le
      have hsmall (j : ℕ) (hj : j ≤ N) : ‖v5DivisionCoeff b j‖ ≤ D^(j+1) := by
        induction j with
        | zero =>
          rw [v5DivisionCoeff, pow_one]
          exact (hsmall_a 0 hj).trans (le_add_of_nonneg_right (by positivity))
        | succ j ih =>
          have hpow : 1 ≤ D^(j+1) := one_le_pow₀ hD
          have hM0 : 0 ≤ M := zero_le_one.trans (hC.trans hCM)
          have hj' : (j+1 : ℝ) ≤ (N+1 : ℝ) := by
            exact_mod_cast (show j+1 ≤ N+1 by omega)
          rw [v5DivisionCoeff]
          calc
            _ ≤ ‖b (j+1)‖ + ‖(j+1 : ℂ) * v5DivisionCoeff b j‖ := norm_add_le _ _
            _ ≤ M + (j+1 : ℝ)*D^(j+1) := by
              rw [norm_mul, ← Nat.cast_add_one, Complex.norm_natCast, Nat.cast_add, Nat.cast_one]
              exact add_le_add (hsmall_a _ hj)
                (mul_le_mul_of_nonneg_left (ih (by omega)) (by positivity))
            _ ≤ M*D^(j+1) + (N+1 : ℝ)*D^(j+1) :=
              add_le_add (le_mul_of_one_le_right hM0 hpow)
                (mul_le_mul_of_nonneg_right hj' (by positivity))
            _ = D^(j+1+1) := by rw [← add_mul, ← pow_succ']
      exact (hsmall n (by omega)).trans (le_mul_of_one_le_right (by positivity) (hpower n ε hε.le))
  · intro L n hn
    have hp := v5_divisionCoeff_integral_prefix (fun j => (a j : ℂ)) (d L) L (hint L) n hn
    have hm := v5_divisionCoeff_map (algebraicClosure ℚ ℂ).val.toRingHom a n
    change IsIntegral ℤ ((d L : ℂ) * (algebraicClosure ℚ ℂ).val.toRingHom (v5DivisionCoeff a n))
    rw [hm]
    exact hp

#print axioms v5_broad_algebraic_division_arithmetic
end StrictEUnit
end
