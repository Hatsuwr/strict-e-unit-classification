import IntegralNormHouse
import Mathlib.Order.Filter.AtTopBot.Finite
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
A genuine factorial-denominator obstruction over the SAME number field.
An exponentially bounded sequence whose factorial normalization admits
exponentially bounded positive integer clearing factors is eventually zero.
This does not assert a differential recurrence, regularity or rational exponents.
-/
noncomputable section
open Filter
open scoped NumberField
namespace StrictEUnit

/-- An algebraic integer with house strictly less than one is zero. -/
theorem isIntegral_eq_zero_of_house_lt_one
    {K : Type*} [Field K] [NumberField K] (x : K)
    (hx : IsIntegral ℤ x) (hsmall : NumberField.house x < 1) : x = 0 := by
  classical
  by_contra hxne
  let v : 𝓞 K := ⟨x, hx⟩
  have hv : v ≠ 0 := by
    intro hz
    apply hxne
    exact congrArg (fun w : 𝓞 K => (w : K)) hz
  obtain ⟨hpos, hbound, hdiv⟩ := ringOfIntegers_natAbs_norm_certificate v hv
  have hone : (1 : ℝ) ≤ (Int.natAbs (Algebra.norm ℤ v) : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hpos)
  have hdeg : Module.finrank ℚ K ≠ 0 :=
    Nat.ne_of_gt (Module.finrank_pos : 0 < Module.finrank ℚ K)
  have hlt : NumberField.house x ^ Module.finrank ℚ K < 1 :=
    pow_lt_one₀ (NumberField.house_nonneg x) hsmall hdeg
  exact (not_le_of_gt hlt) (hone.trans hbound)

/-- A scalar estimate using every complex embedding, not a norm on K. -/
theorem numberField_house_nat_mul_div_nat_le
    {K : Type*} [Field K] [NumberField K] (x : K) (d m : ℕ) :
    NumberField.house ((d : K) * x / (m : K)) ≤
      (d : ℝ) * NumberField.house x / (m : ℝ) := by
  change ‖NumberField.canonicalEmbedding K ((d : K) * x / (m : K))‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg
    (div_nonneg (mul_nonneg (Nat.cast_nonneg d) (NumberField.house_nonneg x))
      (Nat.cast_nonneg m))).2
  intro σ
  change ‖σ ((d : K) * x / (m : K))‖ ≤ _
  simp only [map_div₀, map_mul, map_natCast, Complex.norm_div,
    Complex.norm_mul, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (norm_le_pi_norm (NumberField.canonicalEmbedding K x) σ) (Nat.cast_nonneg d))
    (Nat.cast_nonneg m)

/-- The exact cached natural factorial-domination theorem suffices; no new
analytic limit provider is required. -/
theorem eventually_real_pow_succ_lt_factorial (A : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ n : ℕ in atTop, A ^ (n+1) < (n.factorial : ℝ) := by
  obtain ⟨c, hc⟩ := exists_nat_ge A
  filter_upwards [Nat.eventually_mul_pow_lt_factorial_sub c c 0] with n hn
  have hnat : c * c ^ n < n.factorial := by
    simpa only [Nat.sub_zero] using hn
  have hreal : (c : ℝ) * (c : ℝ) ^ n < (n.factorial : ℝ) := by
    exact_mod_cast hnat
  calc
    A ^ (n+1) ≤ (c : ℝ) ^ (n+1) := pow_le_pow_left₀ hA hc _
    _ = (c : ℝ) * (c : ℝ) ^ n := pow_succ' _ _
    _ < (n.factorial : ℝ) := hreal

/-- The original x, clearing sequence and number field are unchanged.
No eventual-zero, nonvanishing or differential premise is supplied. -/
theorem factorial_denominator_eventually_eq_zero
    {K : Type*} [Field K] [NumberField K]
    (C D : ℝ) (hC : 1 ≤ C) (hD : 1 ≤ D)
    (x : ℕ → K) (δ : ℕ → ℕ) (hδ : ∀ n, 0 < δ n)
    (hδbound : ∀ n, (δ n : ℝ) ≤ D ^ (n+1))
    (hxbound : ∀ n, NumberField.house (x n) ≤ C ^ (n+1))
    (hint : ∀ n, IsIntegral ℤ ((δ n : K) * x n / (n.factorial : K))) :
    ∀ᶠ n : ℕ in atTop, x n = 0 := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  filter_upwards [eventually_real_pow_succ_lt_factorial (D*C) (mul_nonneg hD0 hC0)]
    with n hfact
  have hfpos : (0 : ℝ) < (n.factorial : ℝ) :=
    Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hsmall : NumberField.house ((δ n : K) * x n / (n.factorial : K)) < 1 := by
    calc
      _ ≤ (δ n : ℝ) * NumberField.house (x n) / (n.factorial : ℝ) :=
        numberField_house_nat_mul_div_nat_le (x n) (δ n) n.factorial
      _ ≤ (D ^ (n+1) * C ^ (n+1)) / (n.factorial : ℝ) :=
        div_le_div_of_nonneg_right
          (mul_le_mul (hδbound n) (hxbound n) (NumberField.house_nonneg (x n))
            (pow_nonneg hD0 _)) hfpos.le
      _ = (D*C) ^ (n+1) / (n.factorial : ℝ) := by rw [mul_pow]
      _ < 1 := (div_lt_one hfpos).mpr hfact
  have hz : (δ n : K) * x n / (n.factorial : K) = 0 :=
    isIntegral_eq_zero_of_house_lt_one _ (hint n) hsmall
  have hfne : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hδne : (δ n : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hδ n))
  exact (mul_eq_zero.mp ((div_eq_zero_iff.mp hz).resolve_right hfne)).resolve_left hδne

end StrictEUnit
end
