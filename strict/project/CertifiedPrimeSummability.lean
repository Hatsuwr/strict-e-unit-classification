import FiniteResidueValuationTest
import Mathlib.Topology.Algebra.InfiniteSum.Real

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace StrictEUnit
variable {K Γ₀ : Type*} [Field K] [CharZero K] [LinearOrderedCommGroupWithZero Γ₀]

/-- Binomial arithmetic forces summability on any set of primes carrying
finite residue-unit certificates. This is a consequence, not a prime supply premise. -/
theorem binomialPrefixDenominators_certified_prime_summable
    (a : K) (ha : BinomialPrefixDenominators a)
    (P : Set ℕ) (v : ℕ → Valuation K Γ₀)
    (hp : ∀ p ∈ P, p.Prime) (hvp : ∀ p ∈ P, v p (p : K) < 1)
    (hu : ∀ p ∈ P, ∀ r : ℕ, r < p → v p (a - (r : K)) = 1) :
    Summable (fun p : ℕ => if p ∈ P then Real.log (p : ℝ)/(p : ℝ) else 0) := by
  classical
  obtain ⟨M, hM⟩ := binomialPrefixDenominators_finite_residue_weighted_bound (Γ₀ := Γ₀) a ha
  apply summable_of_sum_le (c := M)
  · intro p
    dsimp only
    split_ifs with h
    · exact div_nonneg (Real.log_nonneg (by exact_mod_cast (hp p h).one_le)) (Nat.cast_nonneg p)
    · exact le_rfl
  · intro S
    rw [← Finset.sum_filter]
    exact hM (S.filter (fun p => p ∈ P)) v
      (fun p h => hp p (Finset.mem_filter.mp h).2)
      (fun p h => hvp p (Finset.mem_filter.mp h).2)
      (fun p h => hu p (Finset.mem_filter.mp h).2)

/-- Explicit conditional obstruction. A divergence theorem and actual local
certificates are both required; neither is inferred from irrationality here. -/
theorem no_binomialPrefixDenominators_of_certified_prime_divergence
    (a : K) (P : Set ℕ) (v : ℕ → Valuation K Γ₀)
    (hp : ∀ p ∈ P, p.Prime) (hvp : ∀ p ∈ P, v p (p : K) < 1)
    (hu : ∀ p ∈ P, ∀ r : ℕ, r < p → v p (a - (r : K)) = 1)
    (hdiv : ¬ Summable (fun p : ℕ => if p ∈ P then Real.log (p : ℝ)/(p : ℝ) else 0)) :
    ¬ BinomialPrefixDenominators a := by
  intro ha
  exact hdiv (binomialPrefixDenominators_certified_prime_summable a ha P v hp hvp hu)

end StrictEUnit
end
