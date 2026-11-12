import OrdinaryPointFundamentalCoefficients

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K]

/-- Exact finite polynomial-product convolution at every coefficient, including
indices below the polynomial degree. -/
theorem coeff_polynomial_mul_range
    (p : Polynomial K) (x : PowerSeries K) (D n : ℕ)
    (hp : p.natDegree ≤ D) :
    PowerSeries.coeff K n ((p : PowerSeries K) * x) =
      ∑ k ∈ Finset.range (D+1),
        if k ≤ n then p.coeff k * PowerSeries.coeff K (n-k) x else 0 := by
  have hrepr : p = ∑ k ∈ Finset.range (D+1),
      Polynomial.C (p.coeff k) * Polynomial.X^k := by
    simpa only [Polynomial.C_mul_X_pow_eq_monomial] using
      p.as_sum_range' (D+1) (Nat.lt_succ_of_le hp)
  calc
    _ = PowerSeries.coeff K n
        ((∑ k ∈ Finset.range (D+1),
          PowerSeries.C K (p.coeff k) * PowerSeries.X^k) * x) := by
      congr 2
      simpa only [map_sum, Polynomial.coeToPowerSeries.ringHom_apply,
        Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow,
        Polynomial.coe_X] using congrArg
          (Polynomial.coeToPowerSeries.ringHom : Polynomial K →+* PowerSeries K) hrepr
    _ = _ := by
      rw [Finset.sum_mul, map_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
      by_cases hkn : k ≤ n <;> simp only [hkn, if_true, if_false, mul_zero]

theorem coeff_polynomial_mul_fin
    (p : Polynomial K) (x : PowerSeries K) (D n : ℕ)
    (hp : p.natDegree ≤ D) :
    PowerSeries.coeff K n ((p : PowerSeries K) * x) =
      ∑ k : Fin (D+1), if k.val ≤ n then
        p.coeff k.val * PowerSeries.coeff K (n-k.val) x else 0 := by
  rw [coeff_polynomial_mul_range p x D n hp]
  exact (Fin.sum_univ_eq_sum_range
    (fun k : ℕ => if k ≤ n then
      p.coeff k * PowerSeries.coeff K (n-k) x else 0) (D+1)).symm

/-- Isolate the ordinary leading coefficient and the genuine positive integer
n+1. Every power-series coefficient on the right has index at most n. -/
theorem clearedPolynomialSystem_coeff_recurrence {r : ℕ}
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (Z : Matrix (Fin r) (Fin r) (PowerSeries K))
    (D : ℕ) (htdeg : t.natDegree ≤ D)
    (hUdeg : ∀ i l, (U i l).natDegree ≤ D)
    (hode : ∀ i j, (t : PowerSeries K) * PowerSeries.derivative K (Z i j) =
      ∑ l : Fin r, (U i l : PowerSeries K) * Z l j)
    (n : ℕ) (i j : Fin r) :
    t.coeff 0 * (n+1 : K) * PowerSeries.coeff K (n+1) (Z i j) =
      (∑ l : Fin r, ∑ k : Fin (D+1), if k.val ≤ n then
        (U i l).coeff k.val * PowerSeries.coeff K (n-k.val) (Z l j) else 0) -
      ∑ k : Fin D, if k.val+1 ≤ n then
        t.coeff (k.val+1) *
          (PowerSeries.coeff K (n-(k.val+1)+1) (Z i j) *
            ((n-(k.val+1)+1 : ℕ) : K)) else 0 := by
  have hc := congrArg (PowerSeries.coeff K n) (hode i j)
  rw [coeff_polynomial_mul_fin t (PowerSeries.derivative K (Z i j)) D n htdeg,
    map_sum] at hc
  simp_rw [coeff_polynomial_mul_fin (U i _) (Z _ j) D n (hUdeg i _)] at hc
  rw [Fin.sum_univ_succ] at hc
  simp only [Fin.val_zero, Fin.val_succ, Nat.zero_le, if_true, Nat.sub_zero] at hc
  simp_rw [PowerSeries.coeff_derivative] at hc
  calc
    _ = t.coeff 0 *
        (PowerSeries.coeff K (n+1) (Z i j) * (n+1 : K)) := by ring
    _ = _ := by
      simpa only [Nat.cast_add, Nat.cast_one] using (eq_sub_iff_add_eq).2 hc

/-- The exact recurrence applies to the already constructed ordinary-point
fundamental matrix, retaining the supplied t,U and alpha. -/
theorem ordinaryPoint_fundamental_coeff_recurrence [CharZero K] {r : ℕ}
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K)) (α : K)
    (hα : t.eval α ≠ 0) (D : ℕ) (htdeg : t.natDegree ≤ D)
    (hUdeg : ∀ i l, (U i l).natDegree ≤ D)
    (n : ℕ) (i j : Fin r) :
    let tα := ordinaryPointPolynomialShift α t
    let Uα : Matrix (Fin r) (Fin r) (Polynomial K) :=
      fun i l => ordinaryPointPolynomialShift α (U i l)
    let Z := formalFundamentalMatrix (ordinaryPointClearedMatrix t U α)
    t.eval α * (n+1 : K) * PowerSeries.coeff K (n+1) (Z i j) =
      (∑ l : Fin r, ∑ k : Fin (D+1), if k.val ≤ n then
        (Uα i l).coeff k.val * PowerSeries.coeff K (n-k.val) (Z l j) else 0) -
      ∑ k : Fin D, if k.val+1 ≤ n then
        tα.coeff (k.val+1) *
          (PowerSeries.coeff K (n-(k.val+1)+1) (Z i j) *
            ((n-(k.val+1)+1 : ℕ) : K)) else 0 :=  by
  let tα := ordinaryPointPolynomialShift α t
  let Uα : Matrix (Fin r) (Fin r) (Polynomial K) :=
    fun i l => ordinaryPointPolynomialShift α (U i l)
  let Z := formalFundamentalMatrix (ordinaryPointClearedMatrix t U α)
  have ht : tα.natDegree ≤ D := by
    rw [ordinaryPointPolynomialShift_natDegree]
    exact htdeg
  have hU : ∀ i l, (Uα i l).natDegree ≤ D := by
    intro i l
    rw [ordinaryPointPolynomialShift_natDegree]
    exact hUdeg i l
  have hode : ∀ i j, (tα : PowerSeries K) * PowerSeries.derivative K (Z i j) =
      ∑ l, (Uα i l : PowerSeries K) * Z l j :=
    ordinaryPointClearedMatrix_fundamental_cleared t U α hα
  have h0 : tα.coeff 0 = t.eval α := by
    exact ordinaryPointPolynomialSeries_constantCoeff α t
  have h := clearedPolynomialSystem_coeff_recurrence tα Uα Z D ht hU hode n i j
  simpa only [h0] using h

end StrictEUnit
end
