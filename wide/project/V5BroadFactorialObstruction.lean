import FactorialDenominatorObstruction

noncomputable section
namespace StrictEUnit
open Filter
open scoped NumberField

/-- A square-root factorial allowance for the common denominator is
compatible with the strict small-house obstruction. No exponential
bound on the denominator itself is assumed. -/
theorem v5_factorial_denominator_eventually_eq_zero_of_square_bound
    {K : Type*} [Field K] [NumberField K]
    (C D : ℝ) (hC : 1 ≤ C) (hD : 1 ≤ D)
    (x : ℕ → K) (δ : ℕ → ℕ) (hδ : ∀ n, 0 < δ n)
    (hδbound : ∀ n, (δ n : ℝ)^2 ≤ D^(n+1) * n.factorial)
    (hxbound : ∀ n, NumberField.house (x n) ≤ C^(n+1))
    (hint : ∀ n, IsIntegral ℤ ((δ n : K) * x n / (n.factorial : K))) :
    ∀ᶠ n : ℕ in atTop, x n = 0 := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  filter_upwards [eventually_real_pow_succ_lt_factorial (D*C^2)
    (mul_nonneg hD0 (sq_nonneg C))] with n hn
  have hfn : (0 : ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hhouse : 0 ≤ NumberField.house (x n) := NumberField.house_nonneg _
  have hd0 : (0 : ℝ) ≤ δ n := Nat.cast_nonneg _
  have hprod : (δ n : ℝ) * NumberField.house (x n) < n.factorial := by
    have hs : ((δ n : ℝ) * NumberField.house (x n))^2 < (n.factorial : ℝ)^2 := by
      calc
        _ = (δ n : ℝ)^2 * NumberField.house (x n)^2 := by ring
        _ ≤ (D^(n+1) * n.factorial) * (C^(n+1))^2 :=
          mul_le_mul (hδbound n) (pow_le_pow_left₀ hhouse (hxbound n) 2)
            (sq_nonneg _) (mul_nonneg (pow_nonneg hD0 _) hfn.le)
        _ = (D*C^2)^(n+1) * n.factorial := by
          rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm (n+1) 2]
          ring
        _ < _ := by simpa only [pow_two] using mul_lt_mul_of_pos_right hn hfn
    apply lt_of_not_ge
    intro hbad
    exact (not_lt_of_ge (pow_le_pow_left₀ hfn.le hbad 2)) hs
  have hsmall : NumberField.house ((δ n : K) * x n / (n.factorial : K)) < 1 :=
    (numberField_house_nat_mul_div_nat_le (x n) (δ n) n.factorial).trans_lt
      ((div_lt_one hfn).mpr hprod)
  have hz := isIntegral_eq_zero_of_house_lt_one _ (hint n) hsmall
  have hfne : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hδne : (δ n : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hδ n))
  exact (mul_eq_zero.mp ((div_eq_zero_iff.mp hz).resolve_right hfne)).resolve_left hδne

#print axioms v5_factorial_denominator_eventually_eq_zero_of_square_bound
end StrictEUnit
end
