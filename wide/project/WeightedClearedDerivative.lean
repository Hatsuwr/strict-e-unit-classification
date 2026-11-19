import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
The differential part of the SAME cleared connection recursion has no
coefficient on or below an irregular weighted face. This is only a local
support lemma. It does not assert the full support induction, constant
companion orbit, arithmetic estimate, or regular singularity.
-/
noncomputable section
namespace StrictEUnit

/-- Differentiation lowers the integer-scaled coefficient weight by at most h.
Neither polynomial must attain its supplied lower support boundary. -/
theorem weighted_cleared_derivative_coeff_eq_zero
    {R : Type*} [CommRing R] (T P : Polynomial R) (c : R)
    (h t e n : ℕ)
    (hT : ∀ i, i < t → T.coeff i = 0)
    (hP : ∀ i, h*i < e → P.coeff i = 0)
    (hn : h*n+h < h*t+e) :
    (T*P.derivative - Polynomial.C c*T.derivative*P).coeff n = 0 := by
  have hleft : (T*P.derivative).coeff n = 0 := by
    rw [Polynomial.coeff_mul]
    apply Finset.sum_eq_zero
    rintro ⟨i,j⟩ hij
    have hij' : i+j=n := Finset.mem_antidiagonal.mp hij
    by_cases hi : i<t
    · rw [hT i hi, zero_mul]
    · have hit : t ≤ i := by omega
      have hmul : h*t ≤ h*i := Nat.mul_le_mul_left h hit
      have heq : h*n+h = h*i+h*(j+1) := by rw [← hij']; ring
      have hj : h*(j+1)<e := by omega
      rw [Polynomial.coeff_derivative, hP (j+1) hj, zero_mul, mul_zero]
  have hright : (T.derivative*P).coeff n = 0 := by
    rw [Polynomial.coeff_mul]
    apply Finset.sum_eq_zero
    rintro ⟨i,j⟩ hij
    have hij' : i+j=n := Finset.mem_antidiagonal.mp hij
    by_cases hi : i+1<t
    · rw [Polynomial.coeff_derivative, hT (i+1) hi, zero_mul, zero_mul]
    · have hit : t ≤ i+1 := by omega
      have hmul : h*t ≤ h*(i+1) := Nat.mul_le_mul_left h hit
      have heq : h*n+h = h*(i+1)+h*j := by rw [← hij']; ring
      have hj : h*j<e := by omega
      rw [hP j hj, mul_zero]
  rw [mul_assoc (Polynomial.C c), Polynomial.coeff_sub,
    Polynomial.coeff_C_mul, hleft, hright, mul_zero, sub_self]

/-- On the face e+(h*t-a), the derivative terms vanish because a>h.
The bound a≤h*t explicitly prevents truncated subtraction changing the face. -/
theorem irregular_cleared_derivative_coeff_eq_zero
    {R : Type*} [CommRing R] (T P : Polynomial R) (c : R)
    (h t e a n : ℕ)
    (hT : ∀ i, i < t → T.coeff i = 0)
    (hP : ∀ i, h*i < e → P.coeff i = 0)
    (hha : h<a) (ha : a≤h*t) (hn : h*n≤e+(h*t-a)) :
    (T*P.derivative - Polynomial.C c*T.derivative*P).coeff n = 0 := by
  apply weighted_cleared_derivative_coeff_eq_zero T P c h t e n hT hP
  omega

end StrictEUnit
end
