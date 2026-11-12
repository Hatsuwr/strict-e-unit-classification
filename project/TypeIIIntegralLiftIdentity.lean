import TypeIIIntegralLiftHouse

/-! Literal identification of the explicit House-bounded truncation lift.
No choice of an unrelated integral representative is made. -/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

theorem typeII_trunc_map_of_contact
    {R K : Type*} [CommRing R] [Field K]
    (φ : R →+* K) (B : Polynomial R) (f : PowerSeries K)
    (b : ℕ → R) (δ : K) (Rcol : Polynomial K) (d L : ℕ)
    (hb : ∀ n, n ≤ d → φ (b n) = δ * PowerSeries.coeff K n f)
    (hdeg : Rcol.natDegree ≤ d) (hdL : d < L)
    (hc : ∀ n, n < L → PowerSeries.coeff K n
      ((B.map φ : PowerSeries K)*f-(Rcol : PowerSeries K)) = 0) :
    (PowerSeries.trunc (d+1) ((B : PowerSeries R)*PowerSeries.mk b)).map φ =
      Polynomial.C δ * Rcol := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_map, Polynomial.coeff_C_mul]
  by_cases hn : n ≤ d
  · have hEq : PowerSeries.coeff K n ((B.map φ : PowerSeries K)*f) = Rcol.coeff n := by
      have h := hc n (lt_of_le_of_lt hn hdL)
      simpa only [map_sub, Polynomial.coeff_coe, sub_eq_zero] using h
    change φ ((PowerSeries.trunc (d+1) ((B : PowerSeries R)*PowerSeries.mk b)).coeff n) = _
    rw [PowerSeries.coeff_trunc, if_pos (by omega)]
    have hm : PowerSeries.coeff K n
        ((B.map φ : PowerSeries K)*PowerSeries.map φ (PowerSeries.mk b)) =
        δ * PowerSeries.coeff K n ((B.map φ : PowerSeries K)*f) := by
      calc
        _ = PowerSeries.coeff K n
            ((B.map φ : PowerSeries K)*(PowerSeries.C K δ*f)) := by
          apply pade_coeff_mul_right_congr
          intro k hk
          rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul]
          exact hb k (hk.trans hn)
        _ = _ := by
          rw [mul_left_comm, PowerSeries.coeff_C_mul]
    rw [hEq] at hm
    simpa only [Polynomial.polynomial_map_coe, ← map_mul, PowerSeries.coeff_map] using hm
  · have hz : Rcol.coeff n = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (by omega))
    change φ ((PowerSeries.trunc (d+1) ((B : PowerSeries R)*PowerSeries.mk b)).coeff n) = _
    rw [PowerSeries.coeff_trunc, if_neg (by omega), map_zero, hz, mul_zero]


/-- The explicit lift maps to δ times the SAME constructed divided column. -/
theorem typeIIIntegralLift_map_column
    {R K : Type*} [CommRing R] [Field K] [CharZero K] {r : ℕ}
    (φ : R →+* K) (T Q : Polynomial R)
    (U : Fin r → Fin r → Polynomial K) (P : Fin r → Polynomial K)
    (f : Fin r → PowerSeries K) (b : Fin r → ℕ → R) (δ : K)
    (N M τ j : ℕ)
    (hT : (T.map φ).natDegree ≤ τ)
    (hU : ∀ i l, (U i l).natDegree ≤ τ)
    (hP : ∀ i, (P i).natDegree ≤ N)
    (hf : ∀ i, (T.map φ : PowerSeries K)*PowerSeries.derivative K (f i) =
      ∑ l, (U i l : PowerSeries K)*f l)
    (hcontact : ∀ i, seriesContact (N+M+1)
      ((Q.map φ : PowerSeries K)*f i-(P i : PowerSeries K)))
    (hb : ∀ i n, n ≤ N+M → φ (b i n) = δ * PowerSeries.coeff K n (f i))
    (hcut : j*(τ+1) ≤ M) (i : Fin r) :
    (typeIIIntegralLift T Q (b i) (N+j*τ) j).map φ =
      Polynomial.C δ * typeIIDividedColumn (T.map φ) U P j i := by
  have hdeg := typeIIDividedColumn_degree (T.map φ) U P N τ hT hU hP j i
  have hc := typeIIColumnError_contact (T.map φ) (Q.map φ) U P f hf
    (N+M+1) hcontact j i
  have hB : (T^j*Polynomial.hasseDeriv j Q).map φ =
      (T.map φ)^j*Polynomial.hasseDeriv j (Q.map φ) := by
    rw [Polynomial.map_mul, Polynomial.map_pow, typeII_hasse_map]
  unfold typeIIIntegralLift
  apply typeII_trunc_map_of_contact φ
    (T^j*Polynomial.hasseDeriv j Q) (f i) (b i) δ _ (N+j*τ) (N+M+1-j)
  · intro n hn
    apply hb i n
    have he : j*(τ+1)=j*τ+j := by rw [Nat.mul_add, Nat.mul_one]
    omega
  · exact hdeg
  · have he : j*(τ+1)=j*τ+j := by rw [Nat.mul_add, Nat.mul_one]
    omega
  · rw [hB]
    exact hc

end StrictEUnit
end
