import MatrixDualBinomial
import Mathlib.Algebra.Polynomial.Derivative

/-! SOURCE ONLY. Polynomial membership of the SAME cleared connection matrices.
No coefficient-integrality, rank, unit-at-zero or denominator-growth theorem. -/
noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {k K B : Type*} [Field k] [Field K] [Field B] [Algebra k B]

/-- W0=I, W(n+1)=T Wn' - n T' Wn + Wn U, with literal polynomial entries. -/
def polynomialConnectionSequence {r : ℕ} (T : Polynomial K)
    (U : Matrix (Fin r) (Fin r) (Polynomial K)) :
    ℕ → Matrix (Fin r) (Fin r) (Polynomial K)
  | 0 => 1
  | n+1 => fun i j => T * (polynomialConnectionSequence T U n i j).derivative -
      (n : Polynomial K) * T.derivative * polynomialConnectionSequence T U n i j +
      ∑ l, polynomialConnectionSequence T U n i l * U l j

/-- A polynomial identity, including n=0, so no division by T is used. -/
theorem mul_derivation_pow (d : Derivation k B B) (t : B) (n : ℕ) :
    t * d (t^n) = (n : B) * t^n * d t := by
  cases n with
  | zero => simp
  | succ n =>
    rw [d.leibniz_pow]
    simp only [Nat.succ_sub_one, nsmul_eq_mul, smul_eq_mul, pow_succ]
    ring

/-- Exact mapping of the constructed polynomial sequence into the original
matrix recurrence. Derivative compatibility is explicit, not assumed automatic. -/
theorem polynomialConnectionSequence_map (d : Derivation k B B)
    (φ : Polynomial K →+* B)
    (hderiv : ∀ p : Polynomial K, d (φ p) = φ p.derivative)
    {r : ℕ} (T : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (A : Matrix (Fin r) (Fin r) B)
    (hclear : ∀ i j, φ (U i j) = φ T * A i j) :
    ∀ n i j, φ (polynomialConnectionSequence T U n i j) =
      (φ T)^n * matrixConnectionSequence d A n i j := by
  classical
  intro n
  induction n with
  | zero =>
    intro i j
    simp only [polynomialConnectionSequence, matrixConnectionSequence, pow_zero, one_mul,
      Matrix.one_apply]
    split_ifs <;> simp
  | succ n ih =>
    intro i j
    have hd : φ ((polynomialConnectionSequence T U n i j).derivative) =
        d ((φ T)^n * matrixConnectionSequence d A n i j) := by
      rw [← hderiv, ih]
    have hsum :
        (∑ l : Fin r, φ (polynomialConnectionSequence T U n i l) * φ (U l j)) =
          (φ T)^(n+1) * ∑ l : Fin r,
            matrixConnectionSequence d A n i l * A l j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      rw [ih, hclear, pow_succ]
      ring
    change φ (T * (polynomialConnectionSequence T U n i j).derivative -
      (n : Polynomial K)*T.derivative*polynomialConnectionSequence T U n i j +
      ∑ l, polynomialConnectionSequence T U n i l*U l j) = _
    simp only [map_add, map_sub, map_mul, map_natCast, map_sum]
    rw [hd, ih, hsum, ← hderiv T]
    change φ T * d ((φ T)^n * matrixConnectionSequence d A n i j) -
      (n : B) * d (φ T) * ((φ T)^n * matrixConnectionSequence d A n i j) +
      (φ T)^(n+1) * (∑ l, matrixConnectionSequence d A n i l * A l j) =
      (φ T)^(n+1) * (d (matrixConnectionSequence d A n i j) +
        ∑ l, matrixConnectionSequence d A n i l * A l j)
    rw [d.leibniz]
    simp only [smul_eq_mul]
    have hp := mul_derivation_pow d (φ T) n
    calc
      _ = (φ T)^(n+1) * (d (matrixConnectionSequence d A n i j) +
          ∑ l, matrixConnectionSequence d A n i l * A l j) +
          (φ T * d ((φ T)^n) - (n : B)*(φ T)^n*d (φ T)) *
            matrixConnectionSequence d A n i j := by
        rw [pow_succ]
        ring
      _ = _ := by rw [hp, sub_self, zero_mul, add_zero]

/-- Divide the polynomial coefficients only by the constant factorial. This
is a polynomial over K; it is not claimed integral over Z. -/
def dividedPolynomialConnectionSequence [CharZero K] {r : ℕ}
    (T : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (n : ℕ) : Matrix (Fin r) (Fin r) (Polynomial K) :=
  fun i j => Polynomial.C ((n.factorial : K)⁻¹) * polynomialConnectionSequence T U n i j

theorem dividedPolynomialConnectionSequence_map [CharZero K]
    (d : Derivation k B B) (φ : Polynomial K →+* B)
    (hderiv : ∀ p : Polynomial K, d (φ p) = φ p.derivative)
    {r : ℕ} (T : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (A : Matrix (Fin r) (Fin r) B)
    (hclear : ∀ i j, φ (U i j) = φ T * A i j) (n : ℕ) :
    ∀ i j, φ (dividedPolynomialConnectionSequence T U n i j) =
      (n.factorial : B)⁻¹ * (φ T)^n * matrixConnectionSequence d A n i j := by
  intro i j
  have hc : φ (Polynomial.C ((n.factorial : K)⁻¹)) = (n.factorial : B)⁻¹ := by
    have he := map_inv₀ (φ.comp Polynomial.C) (n.factorial : K)
    simpa only [RingHom.comp_apply, Polynomial.C_eq_natCast, map_natCast] using he
  simp only [dividedPolynomialConnectionSequence, map_mul, hc,
    polynomialConnectionSequence_map d φ hderiv T U A hclear, mul_assoc]

end StrictEUnit
end
