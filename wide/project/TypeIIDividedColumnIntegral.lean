import TypeIIDividedColumnContact
import PadeMapPrefixTransport
import Mathlib.RingTheory.PowerSeries.Trunc

/-! Source-only. One fixed finite-prefix multiplier δ suffices for ALL columns
inside the explicit contact/degree cutoff. No hypothesis of column integrality. -/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

 theorem typeII_hasse_map {R K : Type*} [CommSemiring R] [CommSemiring K]
    (φ : R →+* K) (Q : Polynomial R) (j : ℕ) :
    (Polynomial.hasseDeriv j Q).map φ = Polynomial.hasseDeriv j (Q.map φ) := by
  ext n
  simp only [Polynomial.coeff_map, Polynomial.hasseDeriv_coeff, map_mul, map_natCast]

/-- Finite-prefix coefficient identification constructs a lift by truncation.
The same δ and same coefficient certificate are used at every column. -/
theorem typeII_integral_polynomial_from_contact
    {R K : Type*} [CommRing R] [Field K]
    (φ : R →+* K) (B : Polynomial R) (f : PowerSeries K)
    (b : ℕ → R) (δ : K) (Rcol : Polynomial K) (d L : ℕ)
    (hb : ∀ n, n ≤ d → φ (b n) = δ * PowerSeries.coeff K n f)
    (hdeg : Rcol.natDegree ≤ d) (hdL : d < L)
    (hc : ∀ n, n < L → PowerSeries.coeff K n
      ((B.map φ : PowerSeries K)*f-(Rcol : PowerSeries K)) = 0) :
    ∃ Z : Polynomial R, Z.map φ = Polynomial.C δ * Rcol := by
  let Z := PowerSeries.trunc (d+1) ((B : PowerSeries R)*PowerSeries.mk b)
  refine ⟨Z, ?_⟩
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

/-- Genuine simultaneous integrality of the constructed divided column after
ONE δ. Q,T are integral polynomials; U and P may be field polynomials. -/
theorem typeII_simultaneous_divided_column_integral
    {R K : Type*} [CommRing R] [Field K] [CharZero K] {r : ℕ}
    (φ : R →+* K) (T Q : Polynomial R)
    (U : Fin r → Fin r → Polynomial K) (P : Fin r → Polynomial K)
    (f : Fin r → PowerSeries K) (b : Fin r → ℕ → R) (δ : K)
    (N M τ s : ℕ)
    (hT : (T.map φ).natDegree ≤ τ)
    (hU : ∀ i l, (U i l).natDegree ≤ τ)
    (hP : ∀ i, (P i).natDegree ≤ N)
    (hf : ∀ i, (T.map φ : PowerSeries K)*PowerSeries.derivative K (f i) =
      ∑ l, (U i l : PowerSeries K)*f l)
    (hcontact : ∀ i, seriesContact (N+M+1)
      ((Q.map φ : PowerSeries K)*f i-(P i : PowerSeries K)))
    (hb : ∀ i n, n ≤ N+M → φ (b i n) = δ * PowerSeries.coeff K n (f i))
    (hcut : s*(τ+1) ≤ M) :
    ∃ Z : ℕ → Fin r → Polynomial R, ∀ j, j ≤ s → ∀ i,
      (Z j i).map φ = Polynomial.C δ *
        typeIIDividedColumn (T.map φ) U P j i := by
  classical
  have hex (j : ℕ) (hj : j ≤ s) (i : Fin r) : ∃ Z : Polynomial R,
      Z.map φ = Polynomial.C δ * typeIIDividedColumn (T.map φ) U P j i := by
    have hjcut : j*(τ+1) ≤ M := (Nat.mul_le_mul_right (τ+1) hj).trans hcut
    have hdeg := typeIIDividedColumn_degree (T.map φ) U P N τ hT hU hP j i
    have hc := typeIIColumnError_contact (T.map φ) (Q.map φ) U P f hf
      (N+M+1) hcontact j i
    have hB : (T^j*Polynomial.hasseDeriv j Q).map φ =
        (T.map φ)^j*Polynomial.hasseDeriv j (Q.map φ) := by
      rw [Polynomial.map_mul, Polynomial.map_pow, typeII_hasse_map]
    apply typeII_integral_polynomial_from_contact φ
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
  choose Z hZ using fun j : Fin (s+1) => fun i => hex j.val (by omega) i
  refine ⟨fun j i => if hj : j ≤ s then Z ⟨j,by omega⟩ i else 0, ?_⟩
  intro j hj i
  simp only [dif_pos hj]
  exact hZ ⟨j,by omega⟩ i

end StrictEUnit
end
