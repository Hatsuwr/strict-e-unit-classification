import Mathlib.Algebra.Polynomial.Coeff
import Lean.Elab.Tactic.Omega

/-!
Finite convolution at possibly unattained lower support boundaries.
The offset is kept as an inequality until the nonnegative case is known;
negative putative indices are zero, not truncated polynomial coefficients.
No nonzero, domain, derivative, arithmetic or regularity premise is used.
-/
noncomputable section
namespace StrictEUnit

/-- If P starts at weight b-d and Q starts at l, their product has no
coefficient below the shifted total boundary. The bound for P can be vacuous. -/
theorem polynomial_coeff_mul_eq_zero_of_shifted_lower_bounds
    {R : Type*} [Semiring R] (P Q : Polynomial R) (b d l n : ℕ)
    (hP : ∀ i, i+d<b → P.coeff i = 0)
    (hQ : ∀ j, j<l → Q.coeff j = 0)
    (hn : n+d<b+l) : (P*Q).coeff n = 0 := by
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨i,j⟩ hij
  have hij' : i+j=n := Finset.mem_antidiagonal.mp hij
  by_cases hi : i+d<b
  · rw [hP i hi, zero_mul]
  · have hj : j<l := by omega
    rw [hQ j hj, mul_zero]

/-- At the sum of two lower support boundaries only the boundary pair
contributes. A boundary coefficient itself is allowed to vanish. -/
theorem polynomial_coeff_mul_at_lower_bounds
    {R : Type*} [Semiring R] (P Q : Polynomial R) (a b : ℕ)
    (hP : ∀ i, i<a → P.coeff i = 0)
    (hQ : ∀ j, j<b → Q.coeff j = 0) :
    (P*Q).coeff (a+b) = P.coeff a * Q.coeff b := by
  rw [Polynomial.coeff_mul]
  refine Finset.sum_eq_single (a,b) ?_ ?_
  · rintro ⟨i,j⟩ hij hne
    have hij' : i+j=a+b := Finset.mem_antidiagonal.mp hij
    by_cases hi : i<a
    · rw [hP i hi, zero_mul]
    by_cases hj : j<b
    · rw [hQ j hj, mul_zero]
    have heq : (i,j)=(a,b) := Prod.ext (by omega) (by omega)
    exact (hne heq).elim
  · intro hnot
    exact (hnot (Finset.mem_antidiagonal.mpr rfl)).elim

/-- The guarded boundary formula used by an irregular companion feedback
term. When d>b, n<l and the product coefficient is zero regardless of P_0. -/
theorem polynomial_coeff_mul_at_shifted_lower_bound
    {R : Type*} [Semiring R] (P Q : Polynomial R) (b d l n : ℕ)
    (hP : ∀ i, i+d<b → P.coeff i = 0)
    (hQ : ∀ j, j<l → Q.coeff j = 0)
    (hn : n+d=b+l) :
    (P*Q).coeff n = (if d≤b then P.coeff (b-d) else 0) * Q.coeff l := by
  by_cases hdb : d≤b
  · rw [if_pos hdb]
    have hn' : n=(b-d)+l := by omega
    rw [hn']
    exact polynomial_coeff_mul_at_lower_bounds P Q (b-d) l
      (fun i hi => hP i (by omega)) hQ
  · rw [if_neg hdb, zero_mul]
    exact polynomial_coeff_mul_eq_zero_of_shifted_lower_bounds P Q 0 0 l n
      (by intro i hi; omega) hQ (by omega)

end StrictEUnit
end
