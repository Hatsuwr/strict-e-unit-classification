import Stage26ODERecurrenceSymbol

noncomputable section
open scoped BigOperators
namespace StrictEUnit
open Polynomial
variable {K : Type*} [Field K]

/-- Exact coefficients of every iterated formal derivative. -/
theorem stage26_coeff_iterate_derivative_asc (x : PowerSeries K) (i n : ℕ) :
    PowerSeries.coeff K n ((PowerSeries.derivative K)^[i] x) =
      PowerSeries.coeff K (n + i) x * (ascPochhammer K i).eval ((n : K) + 1) := by
  induction i generalizing n with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', PowerSeries.coeff_derivative, ih,
      ascPochhammer_succ_left]
    simp only [eval_mul, eval_X, eval_comp, eval_add, eval_one, Nat.cast_add, Nat.cast_one]
    rw [show n + 1 + i = n + (i + 1) by omega]
    ring

/-- Falling-factorial version, matching the polynomial recurrence symbol. -/
theorem stage26_coeff_iterate_derivative (x : PowerSeries K) (i n : ℕ) :
    PowerSeries.coeff K n ((PowerSeries.derivative K)^[i] x) =
      (descPochhammer K i).eval ((n + i : ℕ) : K) * PowerSeries.coeff K (n + i) x := by
  rw [stage26_coeff_iterate_derivative_asc, descPochhammer_eval_eq_ascPochhammer]
  simp only [Nat.cast_add, add_sub_cancel_right]
  exact mul_comm _ _

/-- Coefficients of multiplication by a polynomial, with a uniform exponent bound. -/
theorem stage26_coeff_polynomial_mul (p : Polynomial K) (x : PowerSeries K)
    (D n : ℕ) (hp : p.natDegree ≤ D) :
    PowerSeries.coeff K (n + D) ((p : PowerSeries K) * x) =
      ∑ k ∈ Finset.range (D + 1), p.coeff k * PowerSeries.coeff K (n + D - k) x := by
  have hrepr : p = ∑ k ∈ Finset.range (D + 1), C (p.coeff k) * X ^ k := by
    simpa only [C_mul_X_pow_eq_monomial] using p.as_sum_range' (D + 1) (by omega)
  calc
    PowerSeries.coeff K (n + D) ((p : PowerSeries K) * x) =
      PowerSeries.coeff K (n + D)
        ((∑ k ∈ Finset.range (D + 1), PowerSeries.C K (p.coeff k) * PowerSeries.X ^ k) * x) := by
          congr 2
          simpa only [map_sum, coeToPowerSeries.ringHom_apply, coe_mul, coe_C, coe_pow, coe_X] using
            congrArg (Polynomial.coeToPowerSeries.ringHom : Polynomial K →+* PowerSeries K) hrepr
    _ = _ := by
      rw [Finset.sum_mul, map_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
      rw [if_pos (by have := Finset.mem_range.mp hk; omega)]

/-- Exact coefficient recurrence before grouping equal shifts. -/
theorem stage26_ode_coefficient_identity (p : ℕ → Polynomial K) (N D : ℕ)
    (x : PowerSeries K) (hdeg : ∀ i < N, (p i).natDegree ≤ D)
    (hode : ∑ i ∈ Finset.range N,
      (p i : PowerSeries K) * ((PowerSeries.derivative K)^[i] x) = 0) (n : ℕ) :
    ∑ i ∈ Finset.range N, ∑ k ∈ Finset.range (D + 1),
      (p i).coeff k * (stage26_shiftedFalling (D + i - k) i).eval (n : K) *
        PowerSeries.coeff K (n + (D + i - k)) x = 0 := by
  have h := congrArg (PowerSeries.coeff K (n + D)) hode
  rw [map_sum, map_zero] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [stage26_coeff_polynomial_mul _ _ D n (hdeg i (Finset.mem_range.mp hi))]
  apply Finset.sum_congr rfl
  intro k hk
  rw [stage26_coeff_iterate_derivative]
  have hkD : k ≤ D := by have := Finset.mem_range.mp hk; omega
  have heq : n + D - k + i = n + (D + i - k) := by omega
  simp only [stage26_shiftedFalling, eval_comp, eval_add, eval_X, eval_C, ← Nat.cast_add, heq]
  ring

end StrictEUnit
