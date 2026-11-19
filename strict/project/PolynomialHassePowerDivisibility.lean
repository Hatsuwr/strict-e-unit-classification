import Mathlib.Algebra.Polynomial.HasseDeriv
import Lean.Elab.Tactic.Omega

/-!
# The power of a polynomial dividing a Hasse derivative of its power

This integral polynomial statement includes zero polynomials and all orders.
It does not identify a rational-function divided derivative or construct the
scaled quotient-Hasse recurrence. That separate attachment remains open.
-/

noncomputable section

open scoped BigOperators

namespace StrictEUnit

/-- Taking the `a`th Hasse derivative removes at most `a` copies of `T` from
`T^k`. Natural subtraction makes the assertion include `a > k`, and no
nonzero or constant-term condition on `T` is needed. -/
theorem polynomial_pow_sub_dvd_hasseDeriv_pow
    {R : Type*} [CommSemiring R] (T : Polynomial R) (k a : ℕ) :
    T ^ (k - a) ∣ Polynomial.hasseDeriv a (T ^ k) := by
  induction k generalizing a with
  | zero =>
      simp only [Nat.zero_sub, pow_zero, one_dvd]
  | succ k ih =>
      by_cases ha : k + 1 ≤ a
      · rw [Nat.sub_eq_zero_of_le ha, pow_zero]
        exact one_dvd _
      · have hak : a ≤ k := Nat.le_of_lt_succ (Nat.lt_of_not_ge ha)
        rw [pow_succ' T k, Polynomial.hasseDeriv_mul]
        apply Finset.dvd_sum
        intro x hx
        have hsum : x.1 + x.2 = a := Finset.mem_antidiagonal.mp hx
        by_cases hx0 : x.1 = 0
        · have hx2 : x.2 = a := by omega
          rw [hx0, hx2, Polynomial.hasseDeriv_zero']
          have he : k + 1 - a = (k - a) + 1 := by omega
          rw [he, pow_succ']
          exact mul_dvd_mul_left T (ih a)
        · have hxpos : 0 < x.1 := Nat.pos_of_ne_zero hx0
          have he : k + 1 - a ≤ k - x.2 := by omega
          exact dvd_mul_of_dvd_right ((pow_dvd_pow T he).trans (ih x.2)) _

end StrictEUnit

end
