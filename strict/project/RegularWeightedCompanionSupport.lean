import RegularClearedDerivative

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

private theorem regularPolynomialWeight_step (h t a m j : ℕ) :
    irregularPolynomialWeight h t a (m+1) j =
      irregularPolynomialWeight h t a m j+(h*t-a) := by
  unfold irregularPolynomialWeight
  ring

private theorem regularPolynomialWeight_shift (h t a m j : ℕ) (ha : a≤h*t) :
    irregularPolynomialWeight h t a (m+1) (j+1) =
      irregularPolynomialWeight h t a m j+h*t := by
  have hb := Nat.sub_add_cancel ha
  simp only [irregularPolynomialWeight, Nat.add_mul, Nat.one_mul]
  omega

private theorem regularPolynomialWeight_feedback (n h t a m : ℕ)
    (j : Fin (n+1)) (ha : a≤h*t) :
    irregularPolynomialWeight h t a (m+1) j.val+(n+1-j.val)*a =
      h*t+irregularPolynomialWeight h t a m n := by
  have hb := Nat.sub_add_cancel ha
  have hj : (n+1-j.val)*a+j.val*a=n*a+a := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt j.isLt)]
    ring
  simp only [irregularPolynomialWeight, Nat.add_mul, Nat.one_mul]
  omega

/-- Every below-face coefficient of the original expanded numerator row
vanishes. Zero last-row entries impose no trailing-degree inequality. -/
theorem polynomialConnectionSequence_expanded_regular_support
    {K : Type*} [Field K] (n : ℕ) (c : Fin (n+1) → RatFunc K)
    (T : Polynomial K) (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
      algebraMap (Polynomial K) (RatFunc K) T *
        minimalDerivativeCompanion (n+1) c i j)
    (h a : ℕ) (hh : 0<h) (hha : h≤a) (ha : a≤h*T.natTrailingDegree)
    (hV : ∀ j, U (Fin.last n) j ≠ 0 →
      h*T.natTrailingDegree ≤ h*(U (Fin.last n) j).natTrailingDegree+(n+1-j.val)*a) :
    ∀ (m : ℕ) (j : Fin (n+1)) (k : ℕ),
      k < irregularPolynomialWeight h T.natTrailingDegree a m j.val →
      (Polynomial.expand K h (polynomialConnectionSequence T U m 0 j)).coeff k = 0 := by
  classical
  have hTlow : ∀ k, k<h*T.natTrailingDegree → (Polynomial.expand K h T).coeff k=0 := by
    intro k hk
    apply polynomial_expand_shifted_lower_bound T h (h*T.natTrailingDegree) 0 k hh
    · intro i hi
      have hit : i < T.natTrailingDegree := by
        by_contra hnot
        have hm := Nat.mul_le_mul_left h (Nat.le_of_not_gt hnot)
        omega
      exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (p := T) (n := i) hit
    · simpa only [Nat.add_zero] using hk
  have hVlow : ∀ (j : Fin (n+1)) k, k+(n+1-j.val)*a<h*T.natTrailingDegree →
      (Polynomial.expand K h (U (Fin.last n) j)).coeff k=0 := by
    intro j k hk
    apply polynomial_expand_shifted_lower_bound (U (Fin.last n) j) h
      (h*T.natTrailingDegree) ((n+1-j.val)*a) k hh
    · intro i hi
      by_cases hv : U (Fin.last n) j=0
      · rw [hv, Polynomial.coeff_zero]
      · have hit : i < (U (Fin.last n) j).natTrailingDegree := by
          by_contra hnot
          have hm := Nat.mul_le_mul_left h (Nat.le_of_not_gt hnot)
          have hb := hV j hv
          omega
        exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree
          (p := U (Fin.last n) j) (n := i) hit
    · exact hk
  intro m
  induction m with
  | zero =>
    intro j k hk
    by_cases hj : j=0
    · subst j
      simp only [irregularPolynomialWeight, Nat.zero_mul, Nat.zero_add, Fin.val_zero] at hk
      omega
    · simp only [polynomialConnectionSequence, Matrix.one_apply, if_neg (Ne.symm hj),
        map_zero, Polynomial.coeff_zero]
  | succ m ih =>
    intro j k hk
    have hd :
        (Polynomial.expand K h (T*(polynomialConnectionSequence T U m 0 j).derivative -
          (m : Polynomial K)*T.derivative*polynomialConnectionSequence T U m 0 j)).coeff k=0 := by
      have he := regularPolynomialWeight_step h T.natTrailingDegree a m j.val
      have hx := polynomial_expand_derivative_below_regular_face T
        (polynomialConnectionSequence T U m 0 j) (m : K) h T.natTrailingDegree
        (irregularPolynomialWeight h T.natTrailingDegree a m j.val) a k hh
        (fun i hi => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi)
        (ih j) hha ha (by omega)
      simpa only [Polynomial.C_eq_natCast] using hx
    have hf :
        (Polynomial.expand K h (polynomialConnectionSequence T U m 0 (Fin.last n)*
          U (Fin.last n) j)).coeff k=0 := by
      rw [map_mul, mul_comm (Polynomial.expand K h
        (polynomialConnectionSequence T U m 0 (Fin.last n)))
        (Polynomial.expand K h (U (Fin.last n) j))]
      apply polynomial_coeff_mul_eq_zero_of_shifted_lower_bounds
        (Polynomial.expand K h (U (Fin.last n) j))
        (Polynomial.expand K h (polynomialConnectionSequence T U m 0 (Fin.last n)))
        (h*T.natTrailingDegree) ((n+1-j.val)*a)
        (irregularPolynomialWeight h T.natTrailingDegree a m n) k
        (hVlow j) (ih (Fin.last n))
      have he := regularPolynomialWeight_feedback n h T.natTrailingDegree a m j ha
      omega
    have hrow := polynomialConnectionSequence_companion_first_row n c T U hclear m
    cases j using Fin.cases with
    | zero =>
      rw [hrow.1, map_add, Polynomial.coeff_add, hd, hf, zero_add]
    | succ j =>
      have hs :
          (Polynomial.expand K h (polynomialConnectionSequence T U m 0 j.castSucc*T)).coeff k=0 := by
        rw [map_mul]
        apply polynomial_coeff_mul_eq_zero_of_shifted_lower_bounds
          (Polynomial.expand K h (polynomialConnectionSequence T U m 0 j.castSucc))
          (Polynomial.expand K h T)
          (irregularPolynomialWeight h T.natTrailingDegree a m j.val) 0
          (h*T.natTrailingDegree) k
          (fun i hi => ih j.castSucc i (by simpa only [Nat.add_zero] using hi)) hTlow
        have he := regularPolynomialWeight_shift h T.natTrailingDegree a m j.val ha
        change k < irregularPolynomialWeight h T.natTrailingDegree a (m+1) (j.val+1) at hk
        omega
      rw [hrow.2 j, map_add, Polynomial.coeff_add, map_add, Polynomial.coeff_add,
        hd, hs, hf, zero_add, zero_add]

end StrictEUnit
end
