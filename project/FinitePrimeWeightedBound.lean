import FinitePrimeRateBound

noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- Exact conversion of the finite product rate to its weighted prime sum. -/
theorem finite_prime_product_rate_iff (S : Finset ℕ) (hp : ∀ p ∈ S, p.Prime)
    (C : ℝ) (hC : 1 ≤ C) :
    let L := ∏ p ∈ S, p
    (((∏ p ∈ S, p^(L/p) : ℕ) : ℝ) ≤ C^L) ↔
      (∑ p ∈ S, Real.log (p : ℝ) / (p : ℝ)) ≤ Real.log C := by
  dsimp only
  let L := ∏ p ∈ S, p
  have hL : 0 < L := Finset.prod_pos (fun p hps => (hp p hps).pos)
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hCp : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hB : (0 : ℝ) < ((∏ p ∈ S, p^(L/p) : ℕ) : ℝ) := by
    exact_mod_cast (Finset.prod_pos (fun p hps => pow_pos (hp p hps).pos (L/p)))
  have hlog : Real.log ((∏ p ∈ S, p^(L/p) : ℕ) : ℝ) =
      (L : ℝ) * (∑ p ∈ S, Real.log (p : ℝ)/(p : ℝ)) := by
    rw [Nat.cast_prod, Real.log_prod S (fun p => ((p^(L/p) : ℕ) : ℝ)) (fun p hps => by dsimp only; exact_mod_cast (pow_ne_zero (L/p) (hp p hps).ne_zero))]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hps
    rw [Nat.cast_pow, Real.log_pow]
    have hd : p ∣ L := Finset.dvd_prod_of_mem (fun p => p) hps
    have he : ((L/p : ℕ) : ℝ) = (L : ℝ)/(p : ℝ) := by
      exact Nat.cast_div hd (by exact_mod_cast (hp p hps).ne_zero)
    rw [he]
    ring
  rw [← Real.log_le_log_iff hB (pow_pos hCp L), hlog, Real.log_pow]
  exact mul_le_mul_left hLR

/-- Actual binomial prefix arithmetic uniformly bounds every finite set of
obstructing primes. The bound is independent of the chosen prime set/places. -/
theorem binomialPrefixDenominators_weighted_bound
    {K Γ₀ : Type*} [Field K] [CharZero K] [LinearOrderedCommGroupWithZero Γ₀]
    (a : K) (ha : BinomialPrefixDenominators a) :
    ∃ M : ℝ, ∀ (S : Finset ℕ) (v : ℕ → Valuation K Γ₀),
      (∀ p ∈ S, p.Prime) → (∀ p ∈ S, v p (p : K) < 1) →
      (∀ p ∈ S, ∀ j : ℕ, v p (a - (j : K)) = 1) →
      (∑ p ∈ S, Real.log (p : ℝ)/(p : ℝ)) ≤ M := by
  obtain ⟨C, hC, hD⟩ := ha
  refine ⟨Real.log C, ?_⟩
  intro S v hp hvp hu
  exact (finite_prime_product_rate_iff S hp C hC).mp
    (binomial_finite_prime_rate_bound a C hC hD S v hp hvp hu)

end StrictEUnit
end
