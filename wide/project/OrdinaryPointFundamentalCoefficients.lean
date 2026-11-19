import ClearedConnectionSolution
import OrdinaryPointPowerSeries
import FormalFundamentalMatrixUnit
import Stage26ODERecurrenceCoefficients

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K]

/-- Translation of polynomials to ordinary power series, as an actual ring map. -/
def ordinaryPointPolynomialSeriesHom (α : K) : Polynomial K →+* PowerSeries K :=
  Polynomial.coeToPowerSeries.ringHom.comp
    (ordinaryPointPolynomialShift α).toRingEquiv.toRingHom

@[simp] theorem ordinaryPointPolynomialSeriesHom_apply (α : K) (p : Polynomial K) :
    ordinaryPointPolynomialSeriesHom α p = ordinaryPointPolynomialSeries α p := rfl

theorem ordinaryPointPolynomialSeries_derivative (α : K) (p : Polynomial K) :
    PowerSeries.derivative K (ordinaryPointPolynomialSeries α p) =
      ordinaryPointPolynomialSeries α p.derivative := by
  change PowerSeries.derivative K ((ordinaryPointPolynomialShift α p : Polynomial K) :
    PowerSeries K) = ((ordinaryPointPolynomialShift α p.derivative : Polynomial K) :
      PowerSeries K)
  rw [PowerSeries.derivative_coe]
  simp only [ordinaryPointPolynomialShift_apply, Polynomial.derivative_comp,
    Polynomial.derivative_add, Polynomial.derivative_X, Polynomial.derivative_C,
    add_zero, one_mul]

/-- The ordinary connection at the supplied point using the SAME clearing t,U. -/
def ordinaryPointClearedMatrix {r : ℕ} (t : Polynomial K)
    (U : Matrix (Fin r) (Fin r) (Polynomial K)) (α : K) :
    Matrix (Fin r) (Fin r) (PowerSeries K) :=
  fun i j => ordinaryPointPolynomialSeries α (U i j) *
    (ordinaryPointPolynomialSeries α t)⁻¹

/-- The literal normalized formal matrix satisfies the SAME polynomial-cleared
system at every ordinary point of its supplied denominator. -/
theorem ordinaryPointClearedMatrix_fundamental_cleared [CharZero K]
    {r : ℕ} (t : Polynomial K)
    (U : Matrix (Fin r) (Fin r) (Polynomial K)) (α : K)
    (hα : t.eval α ≠ 0) (i j : Fin r) :
    ordinaryPointPolynomialSeries α t *
      PowerSeries.derivative K (formalFundamentalMatrix
        (ordinaryPointClearedMatrix t U α) i j) =
      ∑ l, ordinaryPointPolynomialSeries α (U i l) *
        formalFundamentalMatrix (ordinaryPointClearedMatrix t U α) l j := by
  classical
  have hc : PowerSeries.constantCoeff K (ordinaryPointPolynomialSeries α t) ≠ 0 := by
    rw [ordinaryPointPolynomialSeries_constantCoeff]
    exact hα
  have hd := congrArg (fun M : Matrix (Fin r) (Fin r) (PowerSeries K) => M i j)
    (formalFundamentalMatrix_derivative (ordinaryPointClearedMatrix t U α))
  change PowerSeries.derivative K (formalFundamentalMatrix
      (ordinaryPointClearedMatrix t U α) i j) =
    (ordinaryPointClearedMatrix t U α *
      formalFundamentalMatrix (ordinaryPointClearedMatrix t U α)) i j at hd
  rw [hd, Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  change ordinaryPointPolynomialSeries α t *
    ((ordinaryPointPolynomialSeries α (U i l) * (ordinaryPointPolynomialSeries α t)⁻¹) *
      formalFundamentalMatrix (ordinaryPointClearedMatrix t U α) l j) = _
  calc
    _ = (ordinaryPointPolynomialSeries α t * (ordinaryPointPolynomialSeries α t)⁻¹) *
      (ordinaryPointPolynomialSeries α (U i l) *
        formalFundamentalMatrix (ordinaryPointClearedMatrix t U α) l j) := by ring
    _ = _ := by rw [PowerSeries.mul_inv_cancel _ hc, one_mul]

theorem ordinaryPoint_fundamental_cleared_iterate [CharZero K]
    {r : ℕ} (t : Polynomial K)
    (U : Matrix (Fin r) (Fin r) (Polynomial K)) (α : K)
    (hα : t.eval α ≠ 0) (m : ℕ) (i j : Fin r) :
    (ordinaryPointPolynomialSeries α t)^m *
      (PowerSeries.derivative K)^[m]
        (formalFundamentalMatrix (ordinaryPointClearedMatrix t U α) i j) =
      ∑ l, ordinaryPointPolynomialSeries α
        (polynomialConnectionSequence t U m i l) *
          formalFundamentalMatrix (ordinaryPointClearedMatrix t U α) l j := by
  exact polynomialConnectionSequence_cleared_solution (PowerSeries.derivative K)
    (ordinaryPointPolynomialSeriesHom α)
    (ordinaryPointPolynomialSeries_derivative α) t U
    (fun l => formalFundamentalMatrix (ordinaryPointClearedMatrix t U α) l j)
    (fun l => ordinaryPointClearedMatrix_fundamental_cleared t U α hα l j) m i

/-- Constant term of an iterated derivative: exactly m! times coefficient m. -/
theorem ordinaryPoint_iterate_derivative_constantCoeff (x : PowerSeries K) (m : ℕ) :
    PowerSeries.constantCoeff K ((PowerSeries.derivative K)^[m] x) =
      PowerSeries.coeff K m x * (m.factorial : K) := by
  simpa only [PowerSeries.coeff_zero_eq_constantCoeff, Nat.zero_add,
    Nat.cast_zero, zero_add, ascPochhammer_eval_one] using
    (stage26_coeff_iterate_derivative_asc x m 0)

/-- Exact coefficient identification with the SAME divided polynomial connection
sequence. The factorial is already in that sequence, and occurs only once. -/
theorem ordinaryPoint_fundamental_coeff [CharZero K]
    {r : ℕ} (t : Polynomial K)
    (U : Matrix (Fin r) (Fin r) (Polynomial K)) (α : K)
    (hα : t.eval α ≠ 0) (m : ℕ) (i j : Fin r) :
    PowerSeries.coeff K m
      (formalFundamentalMatrix (ordinaryPointClearedMatrix t U α) i j) =
      (dividedPolynomialConnectionSequence t U m i j).eval α / (t.eval α)^m := by
  classical
  have h := congrArg (PowerSeries.constantCoeff K)
    (ordinaryPoint_fundamental_cleared_iterate t U α hα m i j)
  simp only [map_mul, map_pow, map_sum, ordinaryPointPolynomialSeries_constantCoeff,
    ordinaryPoint_iterate_derivative_constantCoeff] at h
  have hs : (∑ l, (polynomialConnectionSequence t U m i l).eval α *
      PowerSeries.constantCoeff K
        (formalFundamentalMatrix (ordinaryPointClearedMatrix t U α) l j)) =
        (polynomialConnectionSequence t U m i j).eval α := by
    change ((polynomialConnectionSequence t U m).map (fun p => p.eval α) *
      (formalFundamentalMatrix (ordinaryPointClearedMatrix t U α)).map
        (PowerSeries.constantCoeff K)) i j = _
    rw [formalFundamentalMatrix_constantCoeff, Matrix.mul_one]
    rfl
  rw [hs] at h
  have hf : (m.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  apply (eq_div_iff (pow_ne_zero m hα)).2
  simp only [dividedPolynomialConnectionSequence, Polynomial.eval_mul, Polynomial.eval_C]
  apply mul_left_cancel₀ hf
  calc
    (m.factorial : K) *
        (PowerSeries.coeff K m (formalFundamentalMatrix
          (ordinaryPointClearedMatrix t U α) i j) * (t.eval α)^m) =
        (t.eval α)^m *
          (PowerSeries.coeff K m (formalFundamentalMatrix
            (ordinaryPointClearedMatrix t U α) i j) * (m.factorial:K)) := by ring
    _ = (polynomialConnectionSequence t U m i j).eval α := h
    _ = (m.factorial : K) * ((m.factorial : K)⁻¹ *
        (polynomialConnectionSequence t U m i j).eval α) := by
      rw [← mul_assoc, mul_inv_cancel₀ hf, one_mul]

end StrictEUnit
end
