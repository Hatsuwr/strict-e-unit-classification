import DenominatorGeometricGrowthObstruction
import Mathlib.Data.Int.GCD

noncomputable section
namespace StrictEUnit
variable {K Γ₀ : Type*} [Field K] [CharZero K] [LinearOrderedCommGroupWithZero Γ₀]

theorem valuation_natCast_le_one (v : Valuation K Γ₀) (n : ℕ) : v (n : K) ≤ 1 :=
  natCast_mem v.integer n

theorem valuation_intCast_le_one (v : Valuation K Γ₀) (n : ℤ) : v (n : K) ≤ 1 :=
  intCast_mem v.integer n

theorem valuation_coprime_nat_eq_one (v : Valuation K Γ₀) (p n : ℕ)
    (hp : v (p : K) < 1) (hcop : p.Coprime n) : v (n : K) = 1 := by
  apply le_antisymm (valuation_natCast_le_one v n)
  by_contra hn
  have hn' : v (n : K) < 1 := lt_of_not_ge hn
  have hz := Nat.gcd_eq_gcd_ab p n
  rw [hcop.gcd_eq_one] at hz
  have he : (1 : K) = (p : K) * (Nat.gcdA p n : K) + (n : K) * (Nat.gcdB p n : K) := by
    exact_mod_cast hz
  have ha : v ((p : K) * (Nat.gcdA p n : K)) < 1 := by
    rw [map_mul]
    exact (mul_le_mul_left' (valuation_intCast_le_one v _) _).trans_lt (by simpa using hp)
  have hb : v ((n : K) * (Nat.gcdB p n : K)) < 1 := by
    rw [map_mul]
    exact (mul_le_mul_left' (valuation_intCast_le_one v _) _).trans_lt (by simpa using hn')
  have hle := v.map_add ((p : K) * (Nat.gcdA p n : K)) ((n : K) * (Nat.gcdB p n : K))
  rw [← he, map_one] at hle
  exact (not_lt_of_ge hle) (max_lt ha hb)

/-- Normalized prime-power divisibility follows from v(p)<1 alone;
no chosen numerical normalization of the value group is required. -/
theorem valuation_natCast_le_prime_pow_iff (v : Valuation K Γ₀) (p : ℕ)
    (hp : p.Prime) (hvp : v (p : K) < 1) (d k : ℕ) :
    v (d : K) ≤ v (p : K)^k ↔ p^k ∣ d := by
  have hvpos : 0 < v (p : K) := v.pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  induction k generalizing d with
  | zero => simp [valuation_natCast_le_one]
  | succ k ih =>
    constructor
    · intro h
      have hpd : p ∣ d := by
        by_contra hn
        have he := valuation_coprime_nat_eq_one v p d hvp (hp.coprime_iff_not_dvd.mpr hn)
        rw [he] at h
        have hlt : v (p : K)^(k+1) < 1 := pow_lt_one₀ hvpos.le hvp (Nat.succ_ne_zero k)
        exact (not_lt_of_ge h) hlt
      obtain ⟨b, hb⟩ := hpd
      rw [hb, Nat.cast_mul, map_mul, pow_succ'] at h
      have hbk : p^k ∣ b := (ih b).mp ((mul_le_mul_left hvpos).mp h)
      rw [hb, pow_succ']
      exact Nat.mul_dvd_mul_left p hbk
    · rintro ⟨b, hb⟩
      rw [hb, Nat.cast_mul, map_mul, Nat.cast_pow, map_pow]
      simpa only [mul_one] using mul_le_mul_left' (valuation_natCast_le_one v b) (v (p : K)^(k+1))

/-- Every prime power in the factorial must divide the actual clearing
integer at a p-place with nonresonant residue. -/
theorem binomial_denominator_prime_power_dvd (v : Valuation K Γ₀)
    (p : ℕ) (hp : p.Prime) (hvp : v (p : K) < 1) (a : K) (n d k : ℕ)
    (hu : ∀ j, j < n → v (a - (j : K)) = 1)
    (hint : IsIntegral ℤ ((d : K) * ((descPochhammer K n).eval a / (n.factorial : K))))
    (hfact : p^k ∣ n.factorial) : p^k ∣ d := by
  apply (valuation_natCast_le_prime_pow_iff v p hp hvp d k).mp
  exact (binomial_integral_denominator_valuation_le_factorial v a n d hu hint).trans
    ((valuation_natCast_le_prime_pow_iff v p hp hvp n.factorial k).mpr hfact)

end StrictEUnit
end
