import PolynomialCompanionFace

/-!
The exact coefficient recurrence follows from the previously derived support
of the original W_m. The caller supplies integer slope inequalities, not a
support, recurrence, constant-orbit or regularity premise.
-/
noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

/-- Initial row and both coordinate cases of the SAME constant companion
recurrence. Products have the right-row orientation: u_last*beta_j. -/
theorem polynomialConnectionFaceRow_recurrence
    {K : Type*} [Field K] (n : ℕ) (c : Fin (n+1) → RatFunc K)
    (T : Polynomial K) (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
      algebraMap (Polynomial K) (RatFunc K) T *
        minimalDerivativeCompanion (n+1) c i j)
    (h a : ℕ) (hh : 0<h) (hha : h<a) (ha : a≤h*T.natTrailingDegree)
    (hV : ∀ j, U (Fin.last n) j ≠ 0 →
      h*T.natTrailingDegree ≤ h*(U (Fin.last n) j).natTrailingDegree+(n+1-j.val)*a) :
    polynomialConnectionFaceRow n h a T U 0 = (Pi.single 0 1 : Fin (n+1) → K) ∧
    ∀ m,
      polynomialConnectionFaceRow n h a T U (m+1) 0 =
        polynomialConnectionFaceRow n h a T U m (Fin.last n)*polynomialCompanionFace n h a T U 0 ∧
      ∀ j : Fin n, polynomialConnectionFaceRow n h a T U (m+1) j.succ =
        polynomialConnectionFaceRow n h a T U m j.castSucc*T.coeff T.natTrailingDegree +
        polynomialConnectionFaceRow n h a T U m (Fin.last n)*
          polynomialCompanionFace n h a T U j.succ := by
  classical
  have hsupport := polynomialConnectionSequence_expanded_weighted_support
    n c T U hclear h a hh hha ha hV
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
  constructor
  · funext j
    by_cases hj : j=0
    · subst j
      simp [polynomialConnectionFaceRow, irregularPolynomialWeight,
        polynomialConnectionSequence, Matrix.one_apply, Pi.single_apply]
    · simp [polynomialConnectionFaceRow, polynomialConnectionSequence,
        Matrix.one_apply, Pi.single_apply, hj, Ne.symm hj]
  · intro m
    have hd (j : Fin (n+1)) :
        (Polynomial.expand K h (T*(polynomialConnectionSequence T U m 0 j).derivative -
          (m : Polynomial K)*T.derivative*polynomialConnectionSequence T U m 0 j)).coeff
            (irregularPolynomialWeight h T.natTrailingDegree a (m+1) j.val)=0 := by
      have he : irregularPolynomialWeight h T.natTrailingDegree a (m+1) j.val =
          irregularPolynomialWeight h T.natTrailingDegree a m j.val+(h*T.natTrailingDegree-a) := by
        unfold irregularPolynomialWeight
        ring
      have hx := polynomial_expand_irregular_derivative_zero T
        (polynomialConnectionSequence T U m 0 j) (m : K) h T.natTrailingDegree
        (irregularPolynomialWeight h T.natTrailingDegree a m j.val) a
        (irregularPolynomialWeight h T.natTrailingDegree a (m+1) j.val) hh
        (fun i hi => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi)
        (hsupport m j) hha ha (by omega)
      simpa only [Polynomial.C_eq_natCast] using hx
    have hf (j : Fin (n+1)) :
        (Polynomial.expand K h (polynomialConnectionSequence T U m 0 (Fin.last n)*
          U (Fin.last n) j)).coeff
            (irregularPolynomialWeight h T.natTrailingDegree a (m+1) j.val) =
        polynomialConnectionFaceRow n h a T U m (Fin.last n)*polynomialCompanionFace n h a T U j := by
      have hb := Nat.sub_add_cancel ha
      have hj : (n+1-j.val)*a+j.val*a=n*a+a := by
        rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt j.isLt)]
        ring
      have he : irregularPolynomialWeight h T.natTrailingDegree a (m+1) j.val+(n+1-j.val)*a =
          h*T.natTrailingDegree+irregularPolynomialWeight h T.natTrailingDegree a m n := by
        simp only [irregularPolynomialWeight, Nat.add_mul, Nat.one_mul]
        omega
      rw [map_mul, mul_comm (Polynomial.expand K h
        (polynomialConnectionSequence T U m 0 (Fin.last n)))
        (Polynomial.expand K h (U (Fin.last n) j))]
      calc
        _ = polynomialCompanionFace n h a T U j *
            polynomialConnectionFaceRow n h a T U m (Fin.last n) := by
          exact polynomial_coeff_mul_at_shifted_lower_bound
            (Polynomial.expand K h (U (Fin.last n) j))
            (Polynomial.expand K h (polynomialConnectionSequence T U m 0 (Fin.last n)))
            (h*T.natTrailingDegree) ((n+1-j.val)*a)
            (irregularPolynomialWeight h T.natTrailingDegree a m n)
            (irregularPolynomialWeight h T.natTrailingDegree a (m+1) j.val)
            (hVlow j) (hsupport m (Fin.last n)) he
        _ = _ := mul_comm _ _
    have hs (j : Fin n) :
        (Polynomial.expand K h (polynomialConnectionSequence T U m 0 j.castSucc*T)).coeff
            (irregularPolynomialWeight h T.natTrailingDegree a (m+1) j.succ.val) =
        polynomialConnectionFaceRow n h a T U m j.castSucc*T.coeff T.natTrailingDegree := by
      have hb := Nat.sub_add_cancel ha
      have he : irregularPolynomialWeight h T.natTrailingDegree a (m+1) j.succ.val =
          irregularPolynomialWeight h T.natTrailingDegree a m j.val+h*T.natTrailingDegree := by
        simp only [irregularPolynomialWeight, Fin.val_succ, Nat.add_mul, Nat.one_mul]
        omega
      rw [map_mul, he]
      have hx := polynomial_coeff_mul_at_lower_bounds
        (Polynomial.expand K h (polynomialConnectionSequence T U m 0 j.castSucc))
        (Polynomial.expand K h T)
        (irregularPolynomialWeight h T.natTrailingDegree a m j.val)
        (h*T.natTrailingDegree) (hsupport m j.castSucc) hTlow
      simpa only [polynomialConnectionFaceRow, Fin.coe_castSucc,
        Polynomial.coeff_expand_mul' hh] using hx
    have hrow := polynomialConnectionSequence_companion_first_row n c T U hclear m
    constructor
    · change (Polynomial.expand K h (polynomialConnectionSequence T U (m+1) 0 0)).coeff
        (irregularPolynomialWeight h T.natTrailingDegree a (m+1) 0) = _
      have hd0 :
          (Polynomial.expand K h (T*(polynomialConnectionSequence T U m 0 0).derivative -
            (m : Polynomial K)*T.derivative*polynomialConnectionSequence T U m 0 0)).coeff
              (irregularPolynomialWeight h T.natTrailingDegree a (m+1) 0) = 0 := by
        simpa only [Fin.val_zero] using hd (0 : Fin (n+1))
      have hf0 :
          (Polynomial.expand K h (polynomialConnectionSequence T U m 0 (Fin.last n)*
            U (Fin.last n) 0)).coeff
              (irregularPolynomialWeight h T.natTrailingDegree a (m+1) 0) =
          polynomialConnectionFaceRow n h a T U m (Fin.last n)*
            polynomialCompanionFace n h a T U 0 := by
        simpa only [Fin.val_zero] using hf (0 : Fin (n+1))
      rw [hrow.1, map_add, Polynomial.coeff_add, hd0, hf0, zero_add]
    · intro j
      change (Polynomial.expand K h (polynomialConnectionSequence T U (m+1) 0 j.succ)).coeff
        (irregularPolynomialWeight h T.natTrailingDegree a (m+1) j.succ.val) = _
      rw [hrow.2 j, map_add, Polynomial.coeff_add, map_add, Polynomial.coeff_add,
        hd j.succ, hs j, hf j.succ, zero_add]

end StrictEUnit
end
