import ReciprocalSourceArray
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.BigOperators

/-! NEW SOURCE-ONLY, UNCOMPILED. Mechanical degree estimates for the SAME
reciprocal coefficients. No existence of a regular-singular operator is asserted. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K]

theorem reciprocalGaugeCoefficient_natDegree (i k : ℕ) :
    (reciprocalGaugeCoefficient (K := K) i k).natDegree ≤ i+k+1 := by
  induction i generalizing k with
  | zero =>
    by_cases hk : k=0
    · subst k
      simp only [reciprocalGaugeCoefficient, if_pos rfl, if_true, Polynomial.natDegree_X]
      omega
    · simp only [reciprocalGaugeCoefficient, if_neg hk, Polynomial.natDegree_zero]
      omega
  | succ i ih =>
    rw [reciprocalGaugeCoefficient]
    apply le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    · have hd := Polynomial.natDegree_derivative_le (reciprocalGaugeCoefficient (K := K) i k)
      have hb := ih k
      have hm := Polynomial.natDegree_mul_le
        (p := -(Polynomial.X^2 : Polynomial K))
        (q := Polynomial.derivative (reciprocalGaugeCoefficient (K := K) i k))
      simp only [Polynomial.natDegree_neg, Polynomial.natDegree_X_pow] at hm
      omega
    · by_cases hk : k=0
      · simp only [if_pos hk, mul_zero, Polynomial.natDegree_zero]
        omega
      · rw [if_neg hk]
        have hb := ih (k-1)
        have hm := Polynomial.natDegree_mul_le
          (p := (Polynomial.X^2 : Polynomial K))
          (q := reciprocalGaugeCoefficient (K := K) i (k-1))
        simp only [Polynomial.natDegree_X_pow] at hm
        omega

/-- Fixed-degree reversal sends the first nonzero coefficient to the top. -/
theorem reciprocalReflect_top_coeff (d : ℕ) (q : Polynomial K)
    (hd : q.natDegree ≤ d) :
    (Polynomial.reflect d q).coeff (d-q.natTrailingDegree) = q.coeff q.natTrailingDegree := by
  have hr : q.natTrailingDegree ≤ d := le_trans q.natTrailingDegree_le_natDegree hd
  rw [Polynomial.coeff_reflect, Polynomial.revAt_le (Nat.sub_le d _)]
  congr 1
  omega

theorem reciprocalReflect_natDegree_le (d : ℕ) (q : Polynomial K)
    (hd : q.natDegree ≤ d) :
    (Polynomial.reflect d q).natDegree ≤ d-q.natTrailingDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [Polynomial.coeff_reflect]
  by_cases hnd : n ≤ d
  · rw [Polynomial.revAt_le hnd]
    apply Polynomial.coeff_eq_zero_of_lt_natTrailingDegree
    omega
  · rw [Polynomial.revAt_eq_self_of_lt (by omega)]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

theorem reciprocalReflect_natDegree (d : ℕ) (q : Polynomial K)
    (hd : q.natDegree ≤ d) (hq : q ≠ 0) :
    (Polynomial.reflect d q).natDegree = d-q.natTrailingDegree := by
  apply le_antisymm (reciprocalReflect_natDegree_le d q hd)
  apply Polynomial.le_natDegree_of_ne_zero
  rw [reciprocalReflect_top_coeff d q hd]
  exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr hq

theorem reciprocalReflect_leadingCoeff (d : ℕ) (q : Polynomial K)
    (hd : q.natDegree ≤ d) (hq : q ≠ 0) :
    (Polynomial.reflect d q).leadingCoeff = q.coeff q.natTrailingDegree := by
  rw [Polynomial.leadingCoeff, reciprocalReflect_natDegree d q hd hq,
    reciprocalReflect_top_coeff d q hd]

/-- Guarded inequalities do not constrain ord(0), which is represented by 0. -/
def ReciprocalRegularSingularBounds (m : ℕ) (q : Fin (m+1) → Polynomial K) : Prop :=
  ∀ i, q i ≠ 0 → (q (Fin.last m)).natTrailingDegree+i.val ≤ (q i).natTrailingDegree+m

theorem reciprocalSourcePolynomial_natDegree_bound (m : ℕ)
    (q : Fin (m+1) → Polynomial K) (hreg : ReciprocalRegularSingularBounds m q)
    (k : ℕ) :
    (reciprocalSourcePolynomial m (reciprocalCommonDegree m q) q k).natDegree ≤
      reciprocalCommonDegree m q - (q (Fin.last m)).natTrailingDegree + m+k+1 := by
  unfold reciprocalSourcePolynomial
  refine Polynomial.natDegree_sum_le_of_forall_le Finset.univ
    (fun i : Fin (m+1) => Polynomial.reflect (reciprocalCommonDegree m q) (q i) *
      reciprocalGaugeCoefficient (K := K) i.val k) ?_
  intro i hi
  dsimp only
  by_cases hqi : q i=0
  · simp only [hqi, Polynomial.reflect_zero, zero_mul, Polynomial.natDegree_zero]
    omega
  · have hdeg := reciprocalCommonDegree_bound m q i
    have hord := (q i).natTrailingDegree_le_natDegree
    have htop := le_trans (q (Fin.last m)).natTrailingDegree_le_natDegree
      (reciprocalCommonDegree_bound m q (Fin.last m))
    have hr := hreg i hqi
    have hb := reciprocalGaugeCoefficient_natDegree (K := K) i.val k
    have hprod := Polynomial.natDegree_mul_le
      (p := Polynomial.reflect (reciprocalCommonDegree m q) (q i))
      (q := reciprocalGaugeCoefficient (K := K) i.val k)
    rw [reciprocalReflect_natDegree _ _ hdeg hqi] at hprod
    omega

end StrictEUnit
end
