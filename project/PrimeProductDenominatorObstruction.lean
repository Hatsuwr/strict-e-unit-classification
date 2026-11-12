import ValuationPrimePowerDivisibility
import Mathlib.Data.Nat.GCD.BigOperators

noncomputable section
open scoped BigOperators
namespace StrictEUnit

theorem coprime_nat_product_dvd {ι : Type*} (S : Finset ι) (a : ι → ℕ) (d : ℕ)
    (hc : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (a i).Coprime (a j))
    (hd : ∀ i ∈ S, a i ∣ d) : (∏ i ∈ S, a i) ∣ d := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x S hx ih =>
    rw [Finset.prod_insert hx]
    have hcop : (a x).Coprime (∏ i ∈ S, a i) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro i hi
      exact hc x (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)
        (by intro h; subst i; exact hx hi)
    apply hcop.mul_dvd_of_dvd_of_dvd (hd x (Finset.mem_insert_self _ _))
    exact ih (fun i hi j hj hn => hc i (Finset.mem_insert_of_mem hi) j
      (Finset.mem_insert_of_mem hj) hn) (fun i hi => hd i (Finset.mem_insert_of_mem hi))

/-- Distinct prime constraints accumulate into a product, not merely a maximum. -/
theorem prime_power_product_dvd (S : Finset ℕ) (k : ℕ → ℕ) (d : ℕ)
    (hp : ∀ p ∈ S, p.Prime) (hd : ∀ p ∈ S, p^(k p) ∣ d) :
    (∏ p ∈ S, p^(k p)) ∣ d := by
  apply coprime_nat_product_dvd S (fun p => p^(k p)) d ?_ hd
  intro p hps q hqs hn
  exact ((hp p hps).coprime_iff_not_dvd.mpr
    (fun hd => hn ((Nat.dvd_prime (hp q hqs)).mp hd |>.resolve_left (hp p hps).ne_one))).pow _ _

theorem binomial_denominator_prime_product_dvd
    {K Γ₀ : Type*} [Field K] [CharZero K] [LinearOrderedCommGroupWithZero Γ₀]
    (a : K) (n d : ℕ) (S : Finset ℕ) (k : ℕ → ℕ)
    (v : ℕ → Valuation K Γ₀) (hp : ∀ p ∈ S, p.Prime)
    (hvp : ∀ p ∈ S, v p (p : K) < 1)
    (hu : ∀ p ∈ S, ∀ j, j < n → v p (a - (j : K)) = 1)
    (hint : IsIntegral ℤ ((d : K) * ((descPochhammer K n).eval a / (n.factorial : K))))
    (hk : ∀ p ∈ S, p^(k p) ∣ n.factorial) : (∏ p ∈ S, p^(k p)) ∣ d := by
  apply prime_power_product_dvd S k d hp
  intro p hps
  exact binomial_denominator_prime_power_dvd (v p) p (hp p hps) (hvp p hps)
    a n d (k p) (hu p hps) hint (hk p hps)

end StrictEUnit
end
