import V5BorelSupportAssembly

namespace StrictEUnit

/-- Grouping factorial factors into blocks of length lambda. -/
theorem v5_factorial_block_bound (lam n : ℕ) :
    (lam*n).factorial ≤ lam^(lam*n) * n.factorial^lam := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, ← Nat.factorial_mul_ascFactorial]
    calc
      _ ≤ (lam^(lam*n) * n.factorial^lam) * (lam*n+lam)^lam :=
        Nat.mul_le_mul ih (Nat.ascFactorial_le_pow_add (lam*n) lam)
      _ = lam^(lam*(n+1)) * (n+1).factorial^lam := by
        rw [Nat.factorial_succ, Nat.mul_succ, pow_add]
        rw [show lam*n+lam = lam*(n+1) by ring, mul_pow, mul_pow]
        ring

/-- Factorial cutoff loss is absorbed by an exponential constant independent
of s; no positivity assumption on the height sequence is needed. -/
theorem v5_factorial_cutoff_rescale
    (H : ℕ → ℝ) (C : ℝ) (lam k : ℕ) (hlam : 0 < lam) (hC : 1 ≤ C)
    (hH : ∀ L, H L^(lam*k) ≤ C^(L+1) * (L.factorial : ℝ)) (s : ℕ) :
    H (lam*(s+1)-1)^k ≤ (2*C*(lam : ℝ))^(s+1) * (s.factorial : ℝ) := by
  have hC0 : 0 ≤ C := by linarith
  have hL : lam*(s+1)-1+1 = lam*(s+1) := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.mul_pos hlam (Nat.succ_pos s))))
  have hfac : ((lam*(s+1)-1).factorial : ℝ) ≤
      (lam : ℝ)^(lam*(s+1)) * ((s+1).factorial : ℝ)^lam := by
    have hnat := (Nat.factorial_le (Nat.sub_le (lam*(s+1)) 1)).trans
      (v5_factorial_block_bound lam (s+1))
    exact_mod_cast hnat
  have hpow : (H (lam*(s+1)-1)^k)^lam ≤
      (C^(s+1) * (lam : ℝ)^(s+1) * ((s+1).factorial : ℝ))^lam := by
    calc
      _ = H (lam*(s+1)-1)^(lam*k) := by rw [← pow_mul, Nat.mul_comm k lam]
      _ ≤ C^(lam*(s+1)) * ((lam*(s+1)-1).factorial : ℝ) := by
        simpa only [hL] using hH (lam*(s+1)-1)
      _ ≤ C^(lam*(s+1)) *
          ((lam : ℝ)^(lam*(s+1)) * ((s+1).factorial : ℝ)^lam) :=
        mul_le_mul_of_nonneg_left hfac (pow_nonneg hC0 _)
      _ = _ := by
        simp only [mul_pow, ← pow_mul]
        rw [Nat.mul_comm (s+1) lam]
        ring
  have hroot : H (lam*(s+1)-1)^k ≤
      C^(s+1) * (lam : ℝ)^(s+1) * ((s+1).factorial : ℝ) :=
    le_of_pow_le_pow_left₀ (by omega) (by positivity) hpow
  have hs : (s+1 : ℝ) ≤ (2 : ℝ)^(s+1) := by
    exact_mod_cast (Nat.lt_two_pow_self (n := s+1)).le
  calc
    _ ≤ C^(s+1) * (lam : ℝ)^(s+1) * ((s+1).factorial : ℝ) := hroot
    _ = C^(s+1) * (lam : ℝ)^(s+1) * ((s+1 : ℝ) * (s.factorial : ℝ)) := by
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    _ ≤ C^(s+1) * (lam : ℝ)^(s+1) * ((2 : ℝ)^(s+1) * (s.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs (by positivity)) (by positivity)
    _ = _ := by simp only [mul_pow]; ring

/-- An arbitrary real growth constant can be increased to a uniform E at
least one before rescaling the factorial cutoff. -/
theorem v5_factorial_cutoff_rescale_exists
    (H : ℕ → ℝ) (C : ℝ) (lam k : ℕ) (hlam : 0 < lam) (hC : 0 ≤ C)
    (hH : ∀ L, H L^(lam*k) ≤ C^(L+1) * (L.factorial : ℝ)) :
    ∃ E : ℝ, 1 ≤ E ∧ ∀ s,
      H (lam*(s+1)-1)^k ≤ E^(s+1) * (s.factorial : ℝ) := by
  let D := max C 1
  have hD : 1 ≤ D := le_max_right _ _
  have hHD : ∀ L, H L^(lam*k) ≤ D^(L+1) * (L.factorial : ℝ) := by
    intro L
    exact (hH L).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hC (le_max_left _ _) _) (by positivity))
  refine ⟨2*D*(lam : ℝ), ?_, fun s => v5_factorial_cutoff_rescale H D lam k hlam hD hHD s⟩
  have hl : (1 : ℝ) ≤ lam := by exact_mod_cast hlam
  nlinarith

#print axioms v5_factorial_block_bound
#print axioms v5_factorial_cutoff_rescale
#print axioms v5_factorial_cutoff_rescale_exists
end StrictEUnit
