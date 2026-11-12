import PrimeProductDenominatorObstruction
import Mathlib.Data.Nat.Multiplicity

noncomputable section
open scoped BigOperators
namespace StrictEUnit

theorem prime_floor_power_dvd_factorial (p n : ℕ) (hp : p.Prime) :
    p^(n/p) ∣ n.factorial := by
  apply (Nat.Prime.pow_dvd_factorial_iff hp (show Nat.log p n < Nat.log p n + 2 by omega)).mpr
  have h := Finset.single_le_sum (s := Finset.Ico 1 (Nat.log p n + 2))
    (f := fun i => n / p^i) (fun i _ => Nat.zero_le _) (show 1 ∈ Finset.Ico 1 (Nat.log p n + 2) by simp)
  simpa only [pow_one] using h

/-- Finite prime products force a concrete rate bound on any one exponent
with the existing binomial denominator arithmetic. Suitable places are explicit,
and no claim of sufficiently many such primes is hidden here. -/
theorem binomial_finite_prime_rate_bound
    {K Γ₀ : Type*} [Field K] [CharZero K] [LinearOrderedCommGroupWithZero Γ₀]
    (a : K) (C : ℝ) (hC : 1 ≤ C)
    (hD : ∀ N : ℕ, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ C^(N+1) ∧
      ∀ n, n ≤ N → IsIntegral ℤ ((d : K) * ((descPochhammer K n).eval a / (n.factorial : K))))
    (S : Finset ℕ) (v : ℕ → Valuation K Γ₀)
    (hp : ∀ p ∈ S, p.Prime) (hvp : ∀ p ∈ S, v p (p : K) < 1)
    (hu : ∀ p ∈ S, ∀ j : ℕ, v p (a - (j : K)) = 1) :
    let L := ∏ p ∈ S, p
    ((∏ p ∈ S, p^(L/p) : ℕ) : ℝ) ≤ C^L := by
  dsimp only
  let L := ∏ p ∈ S, p
  apply geometric_integer_denominator_rate_bound (∏ p ∈ S, p^(L/p)) L C hC
  intro k
  obtain ⟨d, hd, hb, hi⟩ := hD (L*k)
  refine ⟨d, hd, hb, ?_⟩
  have he : (∏ p ∈ S, p^(L/p))^k = ∏ p ∈ S, p^((L/p)*k) := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro p _
    rw [pow_mul]
  rw [he]
  apply binomial_denominator_prime_product_dvd a (L*k) d S (fun p => (L/p)*k) v hp hvp
    (fun p hps j _ => hu p hps j) (hi _ le_rfl)
  intro p hps
  have hpL : p ∣ L := Finset.dvd_prod_of_mem (fun p => p) hps
  have hdiv : L*k/p = (L/p)*k := by
    rw [Nat.mul_comm L k, Nat.mul_div_assoc k hpL, Nat.mul_comm]
  rw [← hdiv]
  exact prime_floor_power_dvd_factorial p (L*k) (hp p hps)

end StrictEUnit
end
