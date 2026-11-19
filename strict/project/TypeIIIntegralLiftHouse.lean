import IntegralTypeIIPade
import TypeIIDividedColumnIntegral
import Mathlib.Data.Nat.Choose.Bounds

/-! Source-only explicit finite-coefficient bounds for the literal truncation
lift. All multipliers and polynomial inputs are retained, not reselected. -/
noncomputable section
open scoped BigOperators NumberField
namespace StrictEUnit

 theorem typeIIPolynomial_of_coeff {R : Type*} [Semiring R]
    (P : Polynomial R) (m : ℕ) (hm : P.natDegree ≤ m) :
    typeIIPolynomial m (fun k => P.coeff k.val) = P := by
  ext n
  rw [typeIIPolynomial_coeff]
  split_ifs with hn
  · rfl
  · exact (Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hm (by omega))).symm

/-- A prefix bound for one finite convolution, using only deg P≤m. -/
theorem typeII_series_product_house {K : Type*} [Field K] [NumberField K]
    (P : Polynomial (𝓞 K)) (m d : ℕ) (hm : P.natDegree ≤ m)
    (b : ℕ → 𝓞 K) (E H : ℝ) (hE : 0 ≤ E) (hH : 0 ≤ H)
    (hP : ∀ k, NumberField.house (P.coeff k : K) ≤ E)
    (hb : ∀ k, k ≤ d → NumberField.house (b k : K) ≤ H) :
    ∀ n, n ≤ d → NumberField.house
      (PowerSeries.coeff (𝓞 K) n ((P : PowerSeries (𝓞 K))*PowerSeries.mk b) : K)
        ≤ (m+1)*E*H := by
  intro n hn
  let φ : 𝓞 K →+* K := algebraMap (𝓞 K) K
  have hp := typeIIPolynomial_of_coeff P m hm
  change NumberField.house (φ (PowerSeries.coeff (𝓞 K) n
    ((P : PowerSeries (𝓞 K))*PowerSeries.mk b))) ≤ _
  rw [← hp, typeIIPolynomial_mul_coeff, map_sum]
  calc
    _ ≤ ∑ k : Fin (m+1), NumberField.house
        (φ (if k.val ≤ n then P.coeff k.val*b (n-k.val) else 0)) := by
      exact NumberField.house_sum_le_sum_house _ _
    _ ≤ ∑ _k : Fin (m+1), E*H := by
      apply Finset.sum_le_sum
      intro k hk
      by_cases hkn : k.val ≤ n
      · rw [if_pos hkn, map_mul]
        exact (NumberField.house_mul_le _ _).trans
          (mul_le_mul (hP k.val) (hb _ (by omega)) (NumberField.house_nonneg _) hE)
      · rw [if_neg hkn, map_zero]
        simpa [NumberField.house] using mul_nonneg hE hH
    _ = _ := by simp [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_assoc]

 theorem typeII_polynomial_product_house {K : Type*} [Field K] [NumberField K]
    (P Q : Polynomial (𝓞 K)) (m : ℕ) (hm : P.natDegree ≤ m)
    (E H : ℝ) (hE : 0 ≤ E) (hH : 0 ≤ H)
    (hP : ∀ k, NumberField.house (P.coeff k : K) ≤ E)
    (hQ : ∀ k, NumberField.house (Q.coeff k : K) ≤ H) (n : ℕ) :
    NumberField.house ((P*Q).coeff n : K) ≤ (m+1)*E*H := by
  have h := typeII_series_product_house P m n hm Q.coeff E H hE hH hP
    (fun k _ => hQ k) n le_rfl
  have hmk : PowerSeries.mk Q.coeff = (Q : PowerSeries (𝓞 K)) := by
    apply PowerSeries.ext
    intro k
    simp only [PowerSeries.coeff_mk, Polynomial.coeff_coe]
  simpa only [hmk, ← Polynomial.coe_mul, Polynomial.coeff_coe] using h

/-- Fixed-system coefficient bound for all powers of T. -/
theorem typeII_polynomial_power_house {K : Type*} [Field K] [NumberField K]
    (T : Polynomial (𝓞 K)) (e : ℕ) (he : T.natDegree ≤ e)
    (H : ℝ) (hH : 0 ≤ H) (hT : ∀ k, NumberField.house (T.coeff k : K) ≤ H) :
    ∀ j n, NumberField.house ((T^j).coeff n : K) ≤ ((e+1)*H)^j := by
  intro j
  induction j with
  | zero =>
      intro n
      by_cases hn : n=0
      · subst n; simp [NumberField.house]
      · simp [Polynomial.coeff_one, hn, NumberField.house]
  | succ j ih =>
      intro n
      rw [pow_succ']
      have h := typeII_polynomial_product_house T (T^j) e he H (((e+1)*H)^j)
        hH (pow_nonneg (mul_nonneg (by positivity) hH) _) hT ih n
      simpa only [pow_succ', mul_assoc] using h

/-- Hasse coefficients cost at most 2^N, uniformly in the derivative index. -/
theorem typeII_hasse_house {K : Type*} [Field K] [NumberField K]
    (Q : Polynomial (𝓞 K)) (N : ℕ) (hN : Q.natDegree ≤ N)
    (H : ℝ) (hH : 0 ≤ H) (hQ : ∀ n, NumberField.house (Q.coeff n : K) ≤ H)
    (j n : ℕ) :
    NumberField.house ((Polynomial.hasseDeriv j Q).coeff n : K) ≤ (2:ℝ)^N*H := by
  rw [Polynomial.hasseDeriv_coeff]
  by_cases hn : n+j ≤ N
  · have hb : (n+j).choose j ≤ 2^N := by
      apply (Nat.choose_le_choose j hn).trans
      by_cases hz : N=0
      · subst N
        have hj : j = 0 := by omega
        subst j
        simp
      · exact (Nat.choose_le_two_pow N j (Nat.pos_of_ne_zero hz)).le
    have hnat (m : ℕ) : NumberField.house (m : K) = (m : ℝ) := by
      simpa using NumberField.house_intCast (K := K) (m : ℤ)
    change NumberField.house ((algebraMap (𝓞 K) K)
      (((n+j).choose j : 𝓞 K)*Q.coeff (n+j))) ≤ _
    rw [map_mul, map_natCast]
    calc
      _ ≤ NumberField.house ((n+j).choose j : K) * NumberField.house (Q.coeff (n+j) : K) :=
        NumberField.house_mul_le _ _
      _ ≤ (2:ℝ)^N*H := by
        rw [hnat]
        apply mul_le_mul _ (hQ _) (NumberField.house_nonneg _) (by positivity)
        exact_mod_cast hb
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hN (by omega)), mul_zero]
    simpa [NumberField.house] using mul_nonneg (by positivity : (0:ℝ)≤2^N) hH

/-- The explicit lift used in finite-prefix integrality, now publicly named. -/
def typeIIIntegralLift {R : Type*} [CommRing R]
    (T Q : Polynomial R) (b : ℕ → R) (d j : ℕ) : Polynomial R :=
  PowerSeries.trunc (d+1)
    (((T^j*Polynomial.hasseDeriv j Q : Polynomial R) : PowerSeries R)*PowerSeries.mk b)

/-- A coefficient bound for the SAME explicit lift, not for an arbitrary
existential representative. The first factor is fixed when j<r is fixed. -/
theorem typeIIIntegralLift_house {K : Type*} [Field K] [NumberField K]
    (T Q : Polynomial (𝓞 K)) (b : ℕ → 𝓞 K) (e N d j : ℕ)
    (hTdeg : T.natDegree ≤ e) (hQdeg : Q.natDegree ≤ N)
    (HT HQ Hb : ℝ) (hHT : 0 ≤ HT) (hHQ : 0 ≤ HQ) (hHb : 0 ≤ Hb)
    (hT : ∀ n, NumberField.house (T.coeff n : K) ≤ HT)
    (hQ : ∀ n, NumberField.house (Q.coeff n : K) ≤ HQ)
    (hb : ∀ n, n ≤ d → NumberField.house (b n : K) ≤ Hb) :
    ∀ n, NumberField.house ((typeIIIntegralLift T Q b d j).coeff n : K) ≤
      (j*e+1)*(((e+1)*HT)^j)*((N+1)*(2:ℝ)^N*HQ*Hb) := by
  intro n
  unfold typeIIIntegralLift
  rw [PowerSeries.coeff_trunc]
  have hp := typeII_polynomial_power_house T e hTdeg HT hHT hT j
  have hh := typeII_hasse_house Q N hQdeg HQ hHQ hQ j
  have hd : (Polynomial.hasseDeriv j Q).natDegree ≤ N :=
    (Polynomial.natDegree_hasseDeriv_le Q j).trans ((Nat.sub_le _ _).trans hQdeg)
  let c : ℕ → 𝓞 K := fun k => PowerSeries.coeff (𝓞 K) k
    ((Polynomial.hasseDeriv j Q : PowerSeries (𝓞 K))*PowerSeries.mk b)
  have hc : ∀ k, k ≤ d → NumberField.house (c k : K) ≤ (N+1)*(2:ℝ)^N*HQ*Hb := by
    intro k hk
    have h := typeII_series_product_house (Polynomial.hasseDeriv j Q) N d hd b
      ((2:ℝ)^N*HQ) Hb (mul_nonneg (by positivity) hHQ) hHb hh hb k hk
    simpa only [mul_assoc] using h
  have hm : PowerSeries.mk c =
      (Polynomial.hasseDeriv j Q : PowerSeries (𝓞 K))*PowerSeries.mk b := by
    apply PowerSeries.ext
    intro k
    exact PowerSeries.coeff_mk k c
  split_ifs with hn
  · have h := typeII_series_product_house (T^j) (j*e) d
      (Polynomial.natDegree_pow_le_of_le j hTdeg) c
      (((e+1)*HT)^j) ((N+1)*(2:ℝ)^N*HQ*Hb)
      (pow_nonneg (mul_nonneg (by positivity) hHT) _) (by positivity) hp hc n (by omega)
    simpa only [hm, Polynomial.coe_mul, Nat.cast_mul, mul_assoc] using h
  · simpa [NumberField.house] using
      (show (0:ℝ) ≤ (j*e+1)*(((e+1)*HT)^j)*((N+1)*(2:ℝ)^N*HQ*Hb) by positivity)

end StrictEUnit
end
