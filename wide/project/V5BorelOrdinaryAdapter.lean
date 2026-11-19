import V5FormalRowRealization
import Stage26ODERecurrenceCoefficients

namespace StrictEUnit
open scoped BigOperators

noncomputable def v5FactorialCoeff (F : PowerSeries ℂ) (n : ℕ) : ℂ :=
  (n.factorial : ℂ) * PowerSeries.coeff ℂ n F

noncomputable def v5EulerFalling (j : ℕ) (F : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.X ^ j * (PowerSeries.derivative ℂ)^[j] F

theorem v5_factorialCoeff_derivative (F : PowerSeries ℂ) (n : ℕ) :
    v5FactorialCoeff (PowerSeries.derivative ℂ F) n = v5FactorialCoeff F (n+1) := by
  simp only [v5FactorialCoeff, PowerSeries.coeff_derivative, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  ring

theorem v5_factorialCoeff_iterate (F : PowerSeries ℂ) (k n : ℕ) :
    v5FactorialCoeff ((PowerSeries.derivative ℂ)^[k] F) n =
      v5FactorialCoeff F (n+k) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', v5_factorialCoeff_derivative, ih]
    congr 1
    omega

theorem v5_coeff_eulerFalling (F : PowerSeries ℂ) (j n : ℕ) :
    PowerSeries.coeff ℂ n (v5EulerFalling j F) =
      (n.descFactorial j : ℂ) * PowerSeries.coeff ℂ n F := by
  unfold v5EulerFalling
  rw [PowerSeries.coeff_X_pow_mul']
  by_cases h : j ≤ n
  · rw [if_pos h, stage26_coeff_iterate_derivative, Nat.sub_add_cancel h,
      descPochhammer_eval_eq_descFactorial]
  · rw [if_neg h, Nat.descFactorial_eq_zero_iff_lt.mpr (by omega), Nat.cast_zero, zero_mul]

theorem v5_factorialCoeff_eulerFalling (F : PowerSeries ℂ) (j n : ℕ) :
    v5FactorialCoeff (v5EulerFalling j F) n =
      (n.descFactorial j : ℂ) * v5FactorialCoeff F n := by
  unfold v5FactorialCoeff
  rw [v5_coeff_eulerFalling]
  ring

/-- Reversing a nonnegative Borel shift bounded by P corresponds to an actual
iterated derivative of the exponential series. -/
theorem v5_borel_shift_term {B F : PowerSeries ℂ}
    (hBF : ∀ n, PowerSeries.coeff ℂ n B = v5FactorialCoeff F n)
    (P p j n : ℕ) (hp : p ≤ P) :
    v5FactorialCoeff ((PowerSeries.derivative ℂ)^[P-p] (v5EulerFalling j F)) n =
      PowerSeries.coeff ℂ (n+P) (PowerSeries.X^p * v5EulerFalling j B) := by
  rw [v5_factorialCoeff_iterate, v5_factorialCoeff_eulerFalling,
    PowerSeries.coeff_X_pow_mul', if_pos (by omega), v5_coeff_eulerFalling, hBF]
  rw [show n+P-p = n+(P-p) by omega]

/-- The finite shifted Borel equation gives an exact formal equation for the
exponential series. No analytic convergence or operator regularity is assumed
by this coefficient identity. -/
theorem v5_borel_finite_equation_transfer {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (p j : ι → ℕ) (P : ℕ) (hp : ∀ i, p i ≤ P)
    {B F : PowerSeries ℂ}
    (hBF : ∀ n, PowerSeries.coeff ℂ n B = v5FactorialCoeff F n)
    (hB : ∑ i, PowerSeries.C ℂ (c i) *
      (PowerSeries.X ^ p i * v5EulerFalling (j i) B) = 0) :
    (∑ i, PowerSeries.C ℂ (c i) *
      (PowerSeries.derivative ℂ)^[P-p i] (v5EulerFalling (j i) F)) = 0 := by
  ext n
  have h := congrArg (PowerSeries.coeff ℂ (n+P)) hB
  simp only [map_sum, PowerSeries.coeff_C_mul, map_zero] at h ⊢
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  apply (mul_left_cancel₀ hn)
  rw [mul_zero, Finset.mul_sum]
  calc
    _ = ∑ i, c i * v5FactorialCoeff
        ((PowerSeries.derivative ℂ)^[P-p i] (v5EulerFalling (j i) F)) n := by
      apply Finset.sum_congr rfl
      intro i _
      unfold v5FactorialCoeff
      ring
    _ = 0 := by
      simp_rw [v5_borel_shift_term hBF P _ _ n (hp _)]
      exact h

/-- Polynomial row for z^j D^j. -/
noncomputable def v5EulerPolynomialRow (j k : ℕ) : Polynomial ℂ :=
  if k = j then Polynomial.X ^ j else 0

/-- The explicit polynomial row produced by the finite Borel shift reversal. -/
noncomputable def v5BorelPolynomialRow {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (p j : ι → ℕ) (P k : ℕ) : Polynomial ℂ :=
  ∑ i, Polynomial.C (c i) *
    v5TruncatePolynomialRow
      (v5IteratePolynomialRow (v5EulerPolynomialRow (j i)) (j i) (P-p i))
      (j i+(P-p i)) k

/-- A unique maximal support pair gives the expected monomial leading
coefficient, without assuming a differential row with that property. -/
theorem v5_borelPolynomialRow_top {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ℂ) (p j : ι → ℕ) (P m : ℕ) (i₀ : ι)
    (hj : ∀ i, j i ≤ m) (hp : ∀ i, p i ≤ P)
    (hj₀ : j i₀ = m) (hp₀ : p i₀ = 0)
    (hunique : ∀ i, i ≠ i₀ → j i < m ∨ 0 < p i) :
    v5BorelPolynomialRow c p j P (P+m) = Polynomial.C (c i₀) * Polynomial.X^m := by
  unfold v5BorelPolynomialRow
  rw [Finset.sum_eq_single i₀]
  · have hcut : j i₀ + (P-p i₀) = P+m := by omega
    rw [← hcut]
    simp only [v5TruncatePolynomialRow, le_refl, if_true, v5_iteratePolynomialRow_top]
    simp [v5EulerPolynomialRow, hj₀]
  · intro i _ hi
    have hh := hunique i hi
    have hji := hj i
    have hpi := hp i
    have hlt : j i + (P-p i) < P+m := by omega
    simp [v5TruncatePolynomialRow, show ¬ P+m ≤ j i+(P-p i) by omega]
  · simp

theorem v5_borelPolynomialRow_ordinary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ℂ) (p j : ι → ℕ) (P m : ℕ) (i₀ : ι)
    (hj : ∀ i, j i ≤ m) (hp : ∀ i, p i ≤ P)
    (hj₀ : j i₀ = m) (hp₀ : p i₀ = 0)
    (hunique : ∀ i, i ≠ i₀ → j i < m ∨ 0 < p i)
    (hc : c i₀ ≠ 0) {z : ℂ} (hz : z ≠ 0) :
    (v5BorelPolynomialRow c p j P (P+m)).eval z ≠ 0 := by
  rw [v5_borelPolynomialRow_top c p j P m i₀ hj hp hj₀ hp₀ hunique]
  simpa using mul_ne_zero hc (pow_ne_zero m hz)

#print axioms v5_borelPolynomialRow_top
#print axioms v5_borelPolynomialRow_ordinary
#print axioms v5_factorialCoeff_iterate
#print axioms v5_coeff_eulerFalling
#print axioms v5_borel_shift_term
#print axioms v5_borel_finite_equation_transfer
end StrictEUnit
