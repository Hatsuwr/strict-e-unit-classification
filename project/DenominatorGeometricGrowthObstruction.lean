import BinomialValuationObstruction
import Mathlib.Algebra.Order.Archimedean.Basic

noncomputable section
namespace StrictEUnit

/-- A fixed multiplicative obstruction along multiples of L cannot have a
larger exponential rate than the actual geometric denominator bound. -/
theorem geometric_denominator_rate_bound (B C : ℝ) (hB : 0 ≤ B) (hC : 1 ≤ C)
    (L : ℕ) (h : ∀ k : ℕ, B^k ≤ C^(L*k+1)) : B ≤ C^L := by
  by_contra hn
  have hlt : C^L < B := lt_of_not_ge hn
  have hCp : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hCL : 0 < C^L := pow_pos hCp L
  have hratio : 1 < B / C^L := (one_lt_div hCL).mpr hlt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C hratio
  have hb := h k
  rw [pow_add, pow_one, pow_mul] at hb
  have hu : (B / C^L)^k ≤ C := by
    rw [div_pow]
    exact (div_le_iff₀ (pow_pos hCL k)).mpr (by simpa only [mul_comm] using hb)
  exact (not_lt_of_ge hu) hk

/-- Divisibility, rather than an approximate real lower bound, suffices. -/
theorem geometric_integer_denominator_rate_bound (B L : ℕ) (C : ℝ) (hC : 1 ≤ C)
    (h : ∀ k : ℕ, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ C^(L*k+1) ∧ B^k ∣ d) :
    (B : ℝ) ≤ C^L := by
  apply geometric_denominator_rate_bound (B : ℝ) C (Nat.cast_nonneg _) hC L
  intro k
  obtain ⟨d, hd, hb, hdiv⟩ := h k
  have he : B^k ≤ d := Nat.le_of_dvd hd hdiv
  have he' : (B : ℝ)^k ≤ (d : ℝ) := by exact_mod_cast he
  exact he'.trans hb

/-- It is enough to produce ONE finite prime-product obstruction with rate
above C. A full asymptotic prime-density theorem is not part of this step. -/
theorem no_geometric_denominators_of_excess_rate (B L : ℕ) (C : ℝ) (hC : 1 ≤ C)
    (hlarge : C^L < (B : ℝ)) :
    ¬ (∀ k : ℕ, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ C^(L*k+1) ∧ B^k ∣ d) := by
  intro h
  exact (not_lt_of_ge (geometric_integer_denominator_rate_bound B L C hC h)) hlarge

end StrictEUnit
end
