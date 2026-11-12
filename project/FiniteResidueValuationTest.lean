import FinitePrimeWeightedBound

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K Γ₀ : Type*} [Field K] [CharZero K] [LinearOrderedCommGroupWithZero Γ₀]

/-- At a p-place the infinitely many integer translates need only be tested
on the p standard residues. No primality or residue-field identification is needed. -/
theorem valuation_translate_unit_iff_finite (v : Valuation K Γ₀) (p : ℕ)
    (hp : 0 < p) (hvp : v (p : K) < 1) (a : K) :
    (∀ j : ℕ, v (a - (j : K)) = 1) ↔
    (∀ r : ℕ, r < p → v (a - (r : K)) = 1) := by
  constructor
  · intro h r _; exact h r
  · intro h j
    have hr := h (j % p) (Nat.mod_lt j hp)
    have hm : v ((p : K) * (j / p : ℕ)) < 1 := by
      rw [map_mul]
      exact (mul_le_mul_left' (valuation_natCast_le_one v _) _).trans_lt
        (by simpa using hvp)
    have he : a - (j : K) = (a - (j % p : ℕ)) + -((p : K) * (j / p : ℕ)) := by
      have hj : ((j % p : ℕ) : K) + (p : K) * (j / p : ℕ) = (j : K) := by
        exact_mod_cast Nat.mod_add_div j p
      linear_combination hj
    rw [he, v.map_add_eq_of_lt_left (by simpa only [v.map_neg, hr] using hm), hr]

/-- Finite residue certificates suffice for the actual arithmetic bound.
The prime-supply assertion is deliberately not included as a hypothesis. -/
theorem binomialPrefixDenominators_finite_residue_weighted_bound
    (a : K) (ha : BinomialPrefixDenominators a) :
    ∃ M : ℝ, ∀ (S : Finset ℕ) (v : ℕ → Valuation K Γ₀),
      (∀ p ∈ S, p.Prime) → (∀ p ∈ S, v p (p : K) < 1) →
      (∀ p ∈ S, ∀ r : ℕ, r < p → v p (a - (r : K)) = 1) →
      (∑ p ∈ S, Real.log (p : ℝ)/(p : ℝ)) ≤ M := by
  obtain ⟨M, hM⟩ := binomialPrefixDenominators_weighted_bound (Γ₀ := Γ₀) a ha
  refine ⟨M, ?_⟩
  intro S v hp hvp hr
  apply hM S v hp hvp
  intro p hps
  exact (valuation_translate_unit_iff_finite (v p) p (hp p hps).pos
    (hvp p hps) a).mpr (hr p hps)

end StrictEUnit
end
