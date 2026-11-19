import BoundedPolynomialRowOrder
import PowerSeriesMinimalPrefixRemainder

/-!
NEW SOURCE-ONLY attachment to the already accepted literal remainder theorem.
Independence is used ONLY to show that a nonzero polynomial row has nonzero
action. Finite detection and the bound were proved separately without it.
No uniform system degree bound, Type-II rank, or global arithmetic assertion.
-/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- For the same rationally independent embedded family, every nonzero bounded
polynomial row has a nonzero coefficient below one uniform natural bound. -/
theorem powerSeries_independent_bounded_polynomial_row_order
    {K : Type*} [Field K] {r : ℕ} (f : Fin r → PowerSeries K)
    (hli : LinearIndependent (RatFunc K)
      (fun i => HahnSeries.ofPowerSeries ℤ K (f i))) (d : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ P : Fin r → Polynomial K,
      (∀ i, (P i).natDegree ≤ d) → (∃ i, P i ≠ 0) →
      ∃ n < N, PowerSeries.coeff K n (∑ i, (P i : PowerSeries K) * f i) ≠ 0 ∧
        (∑ i, (P i : PowerSeries K) * f i).order ≤ (n : ℕ∞) := by
  obtain ⟨N, hN, hbound⟩ := powerSeries_bounded_polynomial_row_order f d
  refine ⟨N, hN, fun P hdeg hP => ?_⟩
  exact hbound P hdeg (powerSeries_polynomial_row_remainder_ne_zero f hli P hP)

end StrictEUnit
end
