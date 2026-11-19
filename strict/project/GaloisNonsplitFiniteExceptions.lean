import GaloisNonsplitPrimeDivergence

noncomputable section
open scoped NumberField Topology BigOperators
open NumberField Finset Filter
namespace StrictEUnit

theorem galois_nonsplit_reciprocal_not_summable_outside_finite
    (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    [DecidablePred (GaloisCompletelySplitAt K)] (hd : 1 < Module.finrank ℚ K)
    (T : Finset ℕ) :
    ¬Summable (fun p : ℕ => if p.Prime ∧ ¬GaloisCompletelySplitAt K p ∧ p ∉ T
      then 1 / (p : ℝ) else 0) := by
  intro h
  apply galois_nonsplit_reciprocal_not_summable K hd
  apply h.congr_cofinite
  have hev : ∀ᶠ p : ℕ in cofinite, p ∉ T := by
    apply eventually_cofinite.mpr
    simpa using T.finite_toSet
  filter_upwards [hev] with p hp
  simp [hp]

theorem galois_nonsplit_log_weight_not_summable_outside_finite
    (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    [DecidablePred (GaloisCompletelySplitAt K)] (hd : 1 < Module.finrank ℚ K)
    (T : Finset ℕ) :
    ¬Summable (fun p : ℕ => if p.Prime ∧ ¬GaloisCompletelySplitAt K p ∧ p ∉ T
      then Real.log (p : ℝ) / (p : ℝ) else 0) := by
  intro h
  apply galois_nonsplit_reciprocal_not_summable_outside_finite K hd T
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply Summable.of_nonneg_of_le _ _ (h.div_const (Real.log 2))
  · intro p
    split_ifs <;> positivity
  · intro p
    split_ifs with hp
    · have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.1.two_le
      have hlog : Real.log 2 ≤ Real.log (p : ℝ) := Real.log_le_log (by norm_num) hp2
      apply (le_div_iff₀ hl).mpr
      have h := div_le_div_of_nonneg_right hlog (Nat.cast_nonneg p)
      simpa only [one_div_mul_eq_div, mul_comm] using h
    · simp

end StrictEUnit
end
