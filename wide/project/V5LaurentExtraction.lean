import EntirePolynomialGrowth
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Algebra.Polynomial.Laurent

noncomputable section
open scoped Topology
open Filter Set Metric
namespace StrictEUnit

/-- Removing the pole weight produces an entire function. -/
theorem v5_weighted_removable {f : ℂ → ℂ} (m : ℕ)
    (hf : ∀ z ≠ 0, DifferentiableAt ℂ f z)
    (C : ℝ) (hb : ∀ z ≠ 0, ‖z‖ < 1 → ‖z ^ m * f z‖ ≤ C) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z ≠ 0, g z = z ^ m * f z := by
  let F := fun z : ℂ => z ^ m * f z
  let g := Function.update F 0 (limUnder (𝓝[≠] 0) F)
  have hd : DifferentiableOn ℂ F (ball 0 1 \ {0}) := by
    intro z hz
    exact (((differentiableAt_id.pow m).mul (hf z hz.2)).differentiableWithinAt)
  have hbound : BddAbove (norm ∘ F '' (ball 0 1 \ {0})) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact hb z hz.2 (by simpa [mem_ball, dist_zero_right] using hz.1)
  have hg := Complex.differentiableOn_update_limUnder_of_bddAbove
    (ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)) hd hbound
  refine ⟨g, ?_, ?_⟩
  · intro z
    by_cases hz : z = 0
    · subst z
      exact hg.differentiableAt (ball_mem_nhds _ (by norm_num))
    · apply (((differentiableAt_id.pow m).mul (hf z hz))).congr_of_eventuallyEq
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      exact Function.update_of_ne hw _ _
  · intro z hz
    exact Function.update_of_ne hz _ _

/-- A bounded pole weight at zero and polynomial growth of that weight at infinity
produce a polynomial numerator, with degree control. -/
theorem v5_laurent_numerator_of_weighted_growth {f : ℂ → ℂ} (m N : ℕ)
    (hf : ∀ z ≠ 0, DifferentiableAt ℂ f z)
    (C D : ℝ) (hD : 0 ≤ D)
    (hb : ∀ z ≠ 0, ‖z‖ < 1 → ‖z ^ m * f z‖ ≤ C)
    (hg : ∀ z, 1 ≤ ‖z‖ → ‖z ^ m * f z‖ ≤ D * ‖z‖ ^ N) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ N ∧
      ∀ z ≠ 0, f z = P.eval z / z ^ m := by
  obtain ⟨g, hgd, he⟩ := v5_weighted_removable m hf C hb
  obtain ⟨P, hP, hdeg⟩ := entire_polynomial_of_modulus_growth hgd D 0 N (by
    intro z hz
    have hz0 : z ≠ 0 := by intro h; norm_num [h] at hz
    rw [he z hz0]
    simpa using (hg z hz).trans (le_add_of_nonneg_right hD))
  refine ⟨P, hdeg, ?_⟩
  intro z hz
  rw [hP z, he z hz]
  exact (mul_div_cancel_left₀ (f z) (pow_ne_zero m hz)).symm

/-- Polynomial norm growth at both ends gives an actual finite Laurent polynomial. -/
theorem v5_laurent_of_two_ended_growth {f : ℂ → ℂ} (m n : ℕ)
    (hf : ∀ z ≠ 0, DifferentiableAt ℂ f z)
    (C D : ℝ) (hD : 0 ≤ D)
    (hzero : ∀ z ≠ 0, ‖z‖ < 1 → ‖f z‖ ≤ C / ‖z‖ ^ m)
    (hinfty : ∀ z, 1 ≤ ‖z‖ → ‖f z‖ ≤ D * ‖z‖ ^ n) :
    ∃ L : LaurentPolynomial ℂ, ∀ z : ℂˣ,
      LaurentPolynomial.eval₂ (RingHom.id ℂ) z L = f z := by
  obtain ⟨P, hdeg, hP⟩ := v5_laurent_numerator_of_weighted_growth m (m + n) hf C D hD
    (by
      intro z hz hzn
      rw [norm_mul, norm_pow]
      have hh := mul_le_mul_of_nonneg_left (hzero z hz hzn) (pow_nonneg (norm_nonneg z) m)
      have hn : ‖z‖ ^ m ≠ 0 := pow_ne_zero m (norm_ne_zero_iff.mpr hz)
      simpa [mul_div_cancel₀ _ hn] using hh)
    (by
      intro z hz
      rw [norm_mul, norm_pow]
      calc
        ‖z‖ ^ m * ‖f z‖ ≤ ‖z‖ ^ m * (D * ‖z‖ ^ n) :=
          mul_le_mul_of_nonneg_left (hinfty z hz) (pow_nonneg (norm_nonneg z) m)
        _ = D * ‖z‖ ^ (m + n) := by rw [pow_add]; ring)
  refine ⟨Polynomial.toLaurent P * LaurentPolynomial.T (-(m : ℤ)), ?_⟩
  intro z
  rw [map_mul, LaurentPolynomial.eval₂_toLaurent, LaurentPolynomial.eval₂_T_neg_n]
  rw [hP z (Units.ne_zero z)]
  simp only [div_eq_mul_inv, inv_pow, Units.val_inv_eq_inv_val]
  rfl

end StrictEUnit
#print axioms StrictEUnit.v5_weighted_removable
#print axioms StrictEUnit.v5_laurent_numerator_of_weighted_growth

#print axioms StrictEUnit.v5_laurent_of_two_ended_growth
