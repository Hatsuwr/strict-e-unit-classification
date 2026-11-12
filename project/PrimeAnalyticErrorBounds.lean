import SplitPrimeEulerLogBound
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.LSeries.RiemannZeta

noncomputable section
open scoped Topology BigOperators
open Finset Filter
namespace StrictEUnit

theorem reciprocal_rpow_le_reciprocal {p : ℕ} (hp : 1 ≤ p) {s : ℝ} (hs : 1 ≤ s) :
    1 / (p : ℝ)^s ≤ 1 / (p : ℝ) := by
  apply one_div_le_one_div_of_le
  · exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hp)
  · simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp : (1:ℝ) ≤ p) hs

theorem prime_quadratic_error_uniform (d : ℝ) (hd : 0 ≤ d)
    {s : ℝ} (hs : 1 ≤ s) (S : Finset ℕ) (hS : ∀ p ∈ S, 1 ≤ p) :
    ∑ p ∈ S, (d / (p : ℝ)^s)^2 / 2 ≤
      (d^2 / 2) * ∑' n : ℕ, 1 / (n : ℝ)^2 := by
  have hsum : Summable (fun n : ℕ => 1 / (n : ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  calc
    _ ≤ ∑ p ∈ S, (d^2 / 2) * (1 / (p : ℝ)^2) := by
      apply sum_le_sum
      intro p hp
      have h := mul_le_mul_of_nonneg_left (reciprocal_rpow_le_reciprocal (hS p hp) hs) hd
      have h' : d / (p : ℝ)^s ≤ d / (p : ℝ) := by simpa only [mul_one_div] using h
      have hsq := (sq_le_sq₀ (by positivity : 0 ≤ d / (p : ℝ)^s)
        (by positivity : 0 ≤ d / (p : ℝ))).mpr h'
      calc
        _ ≤ (d / (p : ℝ))^2 / 2 := div_le_div_of_nonneg_right hsq (by norm_num)
        _ = _ := by rw [div_pow]; ring
    _ = (d^2 / 2) * ∑ p ∈ S, 1 / (p : ℝ)^2 := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hsum.sum_le_tsum S (fun n _ => by positivity)) (by positivity)

/-- A summable reciprocal-weight complement contributes a uniform bounded
error to every finite prime sum, also for every exponent s>=1. -/
theorem prime_complement_uniform (T : ℕ → Prop) [DecidablePred T]
    (h : Summable (fun p : ℕ => if p.Prime ∧ ¬T p then 1 / (p : ℝ) else 0)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (s : ℝ), 1 ≤ s → ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime) →
      (∑ p ∈ S, 1 / (p : ℝ)^s) ≤ (∑ p ∈ S with T p, 1 / (p : ℝ)^s) + B := by
  let b : ℕ → ℝ := fun p => if p.Prime ∧ ¬T p then 1 / (p : ℝ) else 0
  have hb : ∀ p, 0 ≤ b p := by intro p; dsimp [b]; split_ifs <;> positivity
  refine ⟨∑' p, b p, tsum_nonneg hb, ?_⟩
  intro s hs S hS
  have he : ∑ p ∈ S with ¬T p, 1 / (p : ℝ)^s ≤ ∑' p, b p := by
    calc
      _ ≤ ∑ p ∈ S with ¬T p, b p := by
        apply sum_le_sum
        intro p hp
        have hpS := hS p (mem_filter.mp hp).1
        rw [show b p = 1 / (p : ℝ) from if_pos ⟨hpS, (mem_filter.mp hp).2⟩]
        exact reciprocal_rpow_le_reciprocal hpS.one_lt.le hs
      _ ≤ _ := h.sum_le_tsum _ (fun p _ => hb p)
  have hsplit := sum_filter_add_sum_filter_not S T (fun p => 1 / (p : ℝ)^s)
  rw [← hsplit]
  exact add_le_add_left he _

end StrictEUnit
end
