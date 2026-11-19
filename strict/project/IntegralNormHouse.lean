import IntegralNormDivisor
import Mathlib.NumberTheory.NumberField.House

/-!
# House bound for the absolute integer norm

The bound uses all complex embeddings of the number field, not a Galois
hypothesis or a bound for an integral basis. The positive natural number is
exactly the absolute value of the signed integer norm already constructed.
-/

noncomputable section

open scoped NumberField BigOperators

namespace StrictEUnit

/-- The absolute integer norm is bounded by the house to the field degree.
The estimate also includes the zero element. -/
theorem ringOfIntegers_natAbs_norm_le_house
    {K : Type*} [Field K] [NumberField K] (v : 𝓞 K) :
    (Int.natAbs (Algebra.norm ℤ v) : ℝ) ≤
      NumberField.house (v : K) ^ Module.finrank ℚ K := by
  classical
  have hnorm : (Algebra.norm ℤ v : ℂ) = ∏ σ : K →ₐ[ℚ] ℂ, σ (v : K) := by
    calc
      (Algebra.norm ℤ v : ℂ) = algebraMap ℚ ℂ (Algebra.norm ℚ (v : K)) := by
        rw [← Algebra.coe_norm_int v]
        simp only [map_intCast]
      _ = ∏ σ : K →ₐ[ℚ] ℂ, σ (v : K) :=
        Algebra.norm_eq_prod_embeddings (K := ℚ) (E := ℂ) (v : K)
  calc
    (Int.natAbs (Algebra.norm ℤ v) : ℝ) = ‖(Algebra.norm ℤ v : ℂ)‖ := by
      simp only [Complex.norm_intCast, Int.cast_natAbs, Int.cast_abs]
    _ = ‖∏ σ : K →ₐ[ℚ] ℂ, σ (v : K)‖ := congrArg norm hnorm
    _ = ∏ σ : K →ₐ[ℚ] ℂ, ‖σ (v : K)‖ := Complex.norm_prod _ _
    _ ≤ ∏ _ : K →ₐ[ℚ] ℂ, NumberField.house (v : K) := by
      apply Finset.prod_le_prod
      · intro σ hσ
        exact norm_nonneg _
      · intro σ hσ
        exact norm_le_pi_norm (NumberField.canonicalEmbedding K (v : K)) σ.toRingHom
    _ = NumberField.house (v : K) ^ Module.finrank ℚ K := by
      rw [Finset.prod_const, Finset.card_univ, AlgHom.card]

/-- For a nonzero algebraic integer, the same absolute integer norm is positive,
has the house bound, and is divisible by the original algebraic integer. -/
theorem ringOfIntegers_natAbs_norm_certificate
    {K : Type*} [Field K] [NumberField K] (v : 𝓞 K) (hv : v ≠ 0) :
    0 < Int.natAbs (Algebra.norm ℤ v) ∧
      (Int.natAbs (Algebra.norm ℤ v) : ℝ) ≤
        NumberField.house (v : K) ^ Module.finrank ℚ K ∧
      v ∣ (Int.natAbs (Algebra.norm ℤ v) : 𝓞 K) := by
  refine ⟨Int.natAbs_pos.mpr (Algebra.norm_ne_zero_iff.mpr hv),
    ringOfIntegers_natAbs_norm_le_house v, ?_⟩
  have hd := ringOfIntegers_dvd_integer_norm v
  rw [Nat.cast_natAbs]
  rcases le_total 0 (Algebra.norm ℤ v) with hn | hn
  · rw [abs_of_nonneg hn]
    exact hd
  · rw [abs_of_nonpos hn, Int.cast_neg]
    exact dvd_neg.mpr hd

end StrictEUnit

end
