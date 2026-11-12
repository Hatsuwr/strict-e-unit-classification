import PrimeAnalyticErrorBounds

noncomputable section
open scoped NumberField nonZeroDivisors BigOperators Topology
open NumberField Finset Filter
namespace StrictEUnit

def GaloisCompletelySplitAt (K : Type*) [Field K] [NumberField K] (p : ℕ) : Prop :=
  Ideal.ramificationIdxIn (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 K) = 1 ∧
  Ideal.inertiaDegIn (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 K) = 1

/-- Under the explicit temporary summability assumption on the nonsplit
complement, every finite ALL-prime sum obeys this analytic constraint. -/
theorem galois_prime_sum_constraint_of_complement_summable
    (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    [DecidablePred (GaloisCompletelySplitAt K)]
    (hcomp : Summable (fun p : ℕ => if p.Prime ∧ ¬GaloisCompletelySplitAt K p
      then 1 / (p : ℝ) else 0)) :
    ∃ C E : ℝ, 0 < C ∧ ∀ s : ℝ, 1 < s → ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime) →
      (Module.finrank ℚ K : ℝ) * (∑ p ∈ S, 1 / (p : ℝ)^s) ≤
        Real.log (s*C/(s-1)) + E := by
  obtain ⟨C, hC, hbound⟩ := galois_split_prime_log_upper_constraint K
  obtain ⟨B, hB, hcompbound⟩ := prime_complement_uniform (GaloisCompletelySplitAt K) hcomp
  let d : ℝ := Module.finrank ℚ K
  let Q : ℝ := (d^2 / 2) * ∑' n : ℕ, 1 / (n : ℝ)^2
  refine ⟨C, Q + d*B, hC, ?_⟩
  intro s hs S hS
  let T := S.filter (GaloisCompletelySplitAt K)
  have hpT : ∀ p ∈ T, p.Prime := fun p hp => hS p (mem_filter.mp hp).1
  have hlog := hbound s hs T hpT
    (fun p hp => (mem_filter.mp hp).2.1)
    (fun p hp => (mem_filter.mp hp).2.2)
  have hquad := prime_quadratic_error_uniform d (Nat.cast_nonneg _) hs.le T
    (fun p hp => (hpT p hp).one_lt.le)
  have hcomp' := mul_le_mul_of_nonneg_left (hcompbound s hs.le S hS) (Nat.cast_nonneg (Module.finrank ℚ K) : 0 ≤ d)
  have hid : (∑ p ∈ T, (d / (p : ℝ)^s - (d / (p : ℝ)^s)^2/2)) =
      d * (∑ p ∈ T, 1 / (p : ℝ)^s) - (∑ p ∈ T, (d / (p : ℝ)^s)^2/2) := by
    rw [sum_sub_distrib, mul_sum]
    simp only [mul_one_div]
  change (∑ p ∈ T, (d / (p : ℝ)^s - (d / (p : ℝ)^s)^2/2)) ≤ _ at hlog
  rw [hid] at hlog
  change (∑ p ∈ T, (d / (p : ℝ)^s)^2/2) ≤ Q at hquad
  change d * (∑ p ∈ S, 1 / (p : ℝ)^s) ≤ d * ((∑ p ∈ T, 1 / (p : ℝ)^s) + B) at hcomp'
  change d * _ ≤ _
  nlinarith

/-- The rational zeta pole gives this concrete lower bound near one. -/
theorem rational_zeta_pole_lower :
    ∀ᶠ s : ℝ in 𝓝[>] 1,
      (1/2 : ℝ) / (s-1) ≤ ∑' n : ℕ, 1 / (n : ℝ)^s := by
  have h := tendsto_sub_mul_tsum_nat_rpow.eventually
    (eventually_gt_nhds (by norm_num : (1/2 : ℝ) < 1))
  filter_upwards [h, self_mem_nhdsWithin] with s hs hpos
  apply (div_le_iff₀ (sub_pos.mpr hpos)).mpr
  nlinarith

end StrictEUnit
end
