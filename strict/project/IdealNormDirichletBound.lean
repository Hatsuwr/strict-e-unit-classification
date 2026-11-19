import IdealNormCoefficients
import LinearSummatoryLSeries

noncomputable section
open scoped NumberField Topology nonZeroDivisors BigOperators
open NumberField Filter Finset Asymptotics
namespace StrictEUnit

/-- The actual ideal-norm Dirichlet series, grouped by positive integer norm. -/
def idealNormLSeries (K : Type*) [Field K] [NumberField K] : ℂ → ℂ :=
  LSeries (fun n => (idealNormCoefficient K n : ℂ))

theorem idealNormCoefficient_global_summatory_bound
    (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      ∑ k ∈ Icc 1 n, (idealNormCoefficient K k : ℝ) ≤ C * n := by
  obtain ⟨C, hC0, hC⟩ := totalIdealCount_global_linear_bound K
  refine ⟨C, hC0, ?_⟩
  intro n hn
  rw [← Nat.cast_sum, idealNormCoefficient_partial_sum]
  exact hC n (by exact_mod_cast hn)

theorem idealNormLSeries_summable
    (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (idealNormCoefficient K n : ℂ)) s := by
  obtain ⟨C, _, hC⟩ := idealNormCoefficient_global_summatory_bound K
  have hf : ∀ n, (0:ℝ) ≤ idealNormCoefficient K n := fun n => Nat.cast_nonneg _
  simpa only [Complex.ofReal_natCast] using
    LSeriesSummable_of_sum_norm_bigO_and_nonneg (linearSummatory_isBigO hf hC) hf
      (by norm_num : (0:ℝ) ≤ 1) hs

/-- Actual geometric ideal counting supplies a simple-pole upper bound.
This does not assert a pole residue or any prime-density conclusion. -/
theorem idealNormLSeries_simple_pole_bound
    (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 1 < s →
      ‖idealNormLSeries K (s : ℂ)‖ ≤ s * C / (s - 1) := by
  obtain ⟨C, hC0, hC⟩ := idealNormCoefficient_global_summatory_bound K
  refine ⟨C, hC0, ?_⟩
  intro s hs
  simpa only [idealNormLSeries, Complex.ofReal_natCast] using
    linearSummatory_LSeries_bound (fun n => Nat.cast_nonneg (idealNormCoefficient K n)) hC0 hC hs

theorem idealNormLSeries_scaled_bound_near_one
    (K : Type*) [Field K] [NumberField K] :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℝ, 1 < s → s ≤ 2 →
      (s - 1) * ‖idealNormLSeries K (s : ℂ)‖ ≤ B := by
  obtain ⟨C, hC0, hC⟩ := idealNormLSeries_simple_pole_bound K
  refine ⟨2 * C, by positivity, ?_⟩
  intro s hs hs2
  have h := (le_div_iff₀ (sub_pos.mpr hs)).mp (hC s hs)
  calc
    _ = ‖idealNormLSeries K (s : ℂ)‖ * (s - 1) := mul_comm _ _
    _ ≤ s * C := h
    _ ≤ 2 * C := mul_le_mul_of_nonneg_right hs2 hC0

end StrictEUnit
end
