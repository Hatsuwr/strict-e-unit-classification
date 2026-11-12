import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Algebraic.Integral

namespace StrictEUnit

/-- An algebraic complex number has a positive natural integral multiplier. -/
theorem algebraic_exists_nat_integral_multiple {z : ℂ} (hz : IsAlgebraic ℚ z) :
    ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : ℂ) * z) := by
  obtain ⟨d, hd, hi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr hz).exists_integral_multiple
  refine ⟨d.natAbs, Int.natAbs_pos.mpr hd, ?_⟩
  rw [Algebra.smul_def] at hi
  change IsIntegral ℤ ((d : ℂ) * z) at hi
  rw [← Int.cast_natCast, Int.natCast_natAbs]
  rcases le_total 0 d with h | h
  · simpa only [abs_of_nonneg h] using hi
  · simpa only [abs_of_nonpos h, Int.cast_neg, neg_mul] using hi.neg

/-- A common positive multiplier for two algebraic complex numbers. -/
theorem algebraic_pair_exists_nat_integral_multiple {α β : ℂ}
    (hα : IsAlgebraic ℚ α) (hβ : IsAlgebraic ℚ β) :
    ∃ D : ℕ, 0 < D ∧ IsIntegral ℤ ((D : ℂ) * α) ∧
      IsIntegral ℤ ((D : ℂ) * β) := by
  obtain ⟨a, ha, ia⟩ := algebraic_exists_nat_integral_multiple hα
  obtain ⟨b, hb, ib⟩ := algebraic_exists_nat_integral_multiple hβ
  have na (n : ℕ) : IsIntegral ℤ (n : ℂ) := by
    exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (n : ℤ)))
  refine ⟨a * b, Nat.mul_pos ha hb, ?_, ?_⟩
  · simpa only [Nat.cast_mul, mul_assoc, mul_left_comm] using (na b).mul ia
  · simpa only [Nat.cast_mul, mul_assoc] using (na a).mul ib

/-- Powers of one common multiplier clear every coefficient through index n. -/
theorem algebraic_geometric_common_denominators {α β : ℂ}
    (hα : IsAlgebraic ℚ α) (hβ : IsAlgebraic ℚ β) :
    ∃ D : ℕ, 0 < D ∧ ∀ n j : ℕ, j ≤ n →
      IsIntegral ℤ (((D ^ (n + 1) : ℕ) : ℂ) * (α * β ^ j)) := by
  obtain ⟨D, hD, iα, iβ⟩ := algebraic_pair_exists_nat_integral_multiple hα hβ
  refine ⟨D, hD, ?_⟩
  intro n j hj
  have iD : IsIntegral ℤ (D : ℂ) := by
    exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (D : ℤ)))
  have hi := (iD.pow (n-j)).mul (iα.mul (iβ.pow j))
  have he : n - j + (j + 1) = n + 1 := by omega
  convert hi using 1
  simp only [Nat.cast_pow, mul_pow]
  calc
    (D : ℂ) ^ (n + 1) * (α * β ^ j) =
        (D : ℂ) ^ (n-j + (j+1)) * (α * β ^ j) := by rw [he]
    _ = (D : ℂ) ^ (n-j) * ((D : ℂ) * α * ((D : ℂ) ^ j * β ^ j)) := by
      rw [pow_add, pow_succ]
      ring

/-- The natural denominators themselves are positive and satisfy an exact
exponential bound, not merely an assumed arithmetic growth condition. -/
theorem algebraic_geometric_denominator_sequence {α β : ℂ}
    (hα : IsAlgebraic ℚ α) (hβ : IsAlgebraic ℚ β) :
    ∃ (D : ℕ) (d : ℕ → ℕ), 0 < D ∧ ∀ n : ℕ,
      0 < d n ∧ d n = D ^ (n + 1) ∧
      (d n : ℝ) ≤ (D : ℝ) ^ (n + 1) ∧
      ∀ j : ℕ, j ≤ n → IsIntegral ℤ ((d n : ℂ) * (α * β ^ j)) := by
  obtain ⟨D, hD, hi⟩ := algebraic_geometric_common_denominators hα hβ
  refine ⟨D, fun n => D ^ (n + 1), hD, ?_⟩
  intro n
  exact ⟨pow_pos hD _, rfl, by simp only [Nat.cast_pow, le_refl], hi n⟩

end StrictEUnit
#print axioms StrictEUnit.algebraic_exists_nat_integral_multiple
#print axioms StrictEUnit.algebraic_pair_exists_nat_integral_multiple
#print axioms StrictEUnit.algebraic_geometric_common_denominators
#print axioms StrictEUnit.algebraic_geometric_denominator_sequence
