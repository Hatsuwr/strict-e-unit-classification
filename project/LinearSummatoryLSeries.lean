import Mathlib.NumberTheory.LSeries.SumCoeff

noncomputable section
open scoped Topology BigOperators
open Filter Finset Asymptotics MeasureTheory
namespace StrictEUnit

theorem linearSummatory_isBigO {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ n, 0 ≤ f n) (hC : ∀ n : ℕ, 1 ≤ n → ∑ k ∈ Icc 1 n, f k ≤ C * n) :
    (fun n ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
  refine isBigO_iff.mpr ⟨C, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  simpa only [Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg (sum_nonneg (fun k _ => hf k)),
    abs_of_nonneg ((Nat.cast_nonneg n : (0:ℝ) ≤ n))] using hC n hn

theorem linearSummatory_LSeries_bound {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ n, 0 ≤ f n) (hC0 : 0 ≤ C)
    (hC : ∀ n : ℕ, 1 ≤ n → ∑ k ∈ Icc 1 n, f k ≤ C * n)
    {s : ℝ} (hs : 1 < s) :
    ‖LSeries (fun n ↦ (f n : ℂ)) (s : ℂ)‖ ≤ s * C / (s - 1) := by
  have hO := linearSummatory_isBigO hf hC
  rw [LSeries_eq_mul_integral_of_nonneg f (by norm_num : (0:ℝ) ≤ 1) (by simpa using hs) hO hf,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < s)]
  have hpow : -s < -1 := by linarith
  have hi := (integrableOn_Ioi_rpow_of_lt hpow zero_lt_one).const_mul C
  have hb : ‖∫ t : ℝ in Set.Ioi 1, (∑ k ∈ Icc 1 ⌊t⌋₊, (f k : ℂ)) *
      (t : ℂ) ^ (-((s : ℂ) + 1))‖ ≤ ∫ t : ℝ in Set.Ioi 1, C * t ^ (-s) := by
    apply norm_integral_le_of_norm_le hi
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    have hn : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by simpa using ht.le)
    have htbound : ∑ k ∈ Icc 1 ⌊t⌋₊, f k ≤ C * t :=
      (hC _ hn).trans (mul_le_mul_of_nonneg_left (Nat.floor_le ht0.le) hC0)
    rw [norm_mul, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sum_nonneg (fun k _ => hf k))]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.one_re]
    calc
      _ ≤ (C * t) * t ^ (-(s + 1)) :=
        mul_le_mul_of_nonneg_right htbound (Real.rpow_nonneg ht0.le _)
      _ = C * t ^ (-s) := by
        rw [mul_assoc]
        congr 1
        calc
          t * t ^ (-(s + 1)) = t ^ (1:ℝ) * t ^ (-(s + 1)) := by rw [Real.rpow_one]
          _ = t ^ ((1:ℝ) + -(s + 1)) := (Real.rpow_add ht0 _ _).symm
          _ = t ^ (-s) := by congr 1 <;> ring
  have hInt : (∫ t : ℝ in Set.Ioi 1, C * t ^ (-s)) = C / (s - 1) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt hpow zero_lt_one, Real.one_rpow]
    rw [show -s + 1 = -(s - 1) by ring, div_neg, neg_div, neg_neg]
    ring
  rw [hInt] at hb
  exact (mul_le_mul_of_nonneg_left hb (by linarith)).trans_eq (by ring)

end StrictEUnit
end
