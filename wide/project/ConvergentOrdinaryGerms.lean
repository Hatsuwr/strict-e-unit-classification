import OrdinaryPointHouseGrowth
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.FDeriv.Analytic

noncomputable section
open scoped Topology BigOperators ENNReal
namespace StrictEUnit

/-- Actual ordinary, not factorial, sum of the supplied coefficient sequence. -/
def ordinaryGermSum (a : ℕ → ℂ) : ℂ → ℂ :=
  (FormalMultilinearSeries.ofScalars ℂ a).sum

/-- Reciprocal of a derived geometric bound, used as a concrete local radius. -/
def ordinaryGermRadius (C : ℝ) (hC : 1 ≤ C) : NNReal :=
  ⟨C⁻¹, inv_nonneg.mpr (le_trans zero_le_one hC)⟩

theorem ordinaryGermRadius_pos (C : ℝ) (hC : 1 ≤ C) :
    0 < ordinaryGermRadius C hC := by
  change (0:ℝ) < C⁻¹
  exact inv_pos.mpr (lt_of_lt_of_le zero_lt_one hC)

theorem ordinaryGerm_radius_le (a : ℕ → ℂ) (C : ℝ) (hC : 1 ≤ C)
    (ha : ∀ n, ‖a n‖ ≤ C^n) :
    (ordinaryGermRadius C hC : ENNReal) ≤
      (FormalMultilinearSeries.ofScalars ℂ a).radius := by
  apply FormalMultilinearSeries.le_radius_of_bound _ 1
  intro n
  rw [FormalMultilinearSeries.ofScalars_norm]
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  calc
    ‖a n‖ * ((ordinaryGermRadius C hC : NNReal):ℝ)^n ≤
        C^n * (C⁻¹)^n :=
      mul_le_mul_of_nonneg_right (ha n) (pow_nonneg (inv_nonneg.mpr (le_of_lt hC0)) n)
    _ = 1 := by rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hC0), one_pow]

/-- The actual sum has its literal ordinary series on a positive disk. -/
theorem ordinaryGerm_hasFPowerSeriesOnBall (a : ℕ → ℂ) (C : ℝ) (hC : 1 ≤ C)
    (ha : ∀ n, ‖a n‖ ≤ C^n) :
    HasFPowerSeriesOnBall (ordinaryGermSum a)
      (FormalMultilinearSeries.ofScalars ℂ a) 0 (ordinaryGermRadius C hC : ENNReal) := by
  have hr : (0:ENNReal) < (ordinaryGermRadius C hC : ENNReal) := by
    exact_mod_cast ordinaryGermRadius_pos C hC
  have hrad := ordinaryGerm_radius_le a C hC ha
  exact ((FormalMultilinearSeries.ofScalars ℂ a).hasFPowerSeriesOnBall
    (hr.trans_le hrad)).mono hr hrad

theorem ordinaryGerm_hasSum (a : ℕ → ℂ) (C : ℝ) (hC : 1 ≤ C)
    (ha : ∀ n, ‖a n‖ ≤ C^n) (z : ℂ)
    (hz : z ∈ EMetric.ball (0:ℂ) (ordinaryGermRadius C hC : ENNReal)) :
    HasSum (fun n => a n * z^n) (ordinaryGermSum a z) := by
  have h := (ordinaryGerm_hasFPowerSeriesOnBall a C hC ha).hasSum hz
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] using h

theorem ordinaryGerm_analyticAt (a : ℕ → ℂ) (C : ℝ) (hC : 1 ≤ C)
    (ha : ∀ n, ‖a n‖ ≤ C^n) (z : ℂ)
    (hz : z ∈ EMetric.ball (0:ℂ) (ordinaryGermRadius C hC : ENNReal)) :
    AnalyticAt ℂ (ordinaryGermSum a) z :=
  (ordinaryGerm_hasFPowerSeriesOnBall a C hC ha).analyticAt_of_mem hz

/-- Every entry of the SAME ordinary fundamental matrix is now an actual
analytic germ, with a common positive radius derived from its house bound. -/
theorem ordinaryPoint_fundamental_analytic_germs
    {K : Type*} [Field K] [NumberField K] {r : ℕ}
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K)) (α : K)
    (hα : t.eval α ≠ 0) (σ : K →+* ℂ) :
    ∃ C : ℝ, ∃ hC : 1 ≤ C,
      ∀ i j : Fin r, HasFPowerSeriesOnBall
        (ordinaryGermSum (fun n => σ (PowerSeries.coeff K n
          (formalFundamentalMatrix (ordinaryPointClearedMatrix t U α) i j))))
        (FormalMultilinearSeries.ofScalars ℂ (fun n => σ (PowerSeries.coeff K n
          (formalFundamentalMatrix (ordinaryPointClearedMatrix t U α) i j))))
        0 (ordinaryGermRadius C hC : ENNReal) := by
  obtain ⟨C,hC,hhouse⟩ := ordinaryPoint_fundamental_house_bound t U α hα
  refine ⟨C,hC,?_⟩
  intro i j
  exact ordinaryGerm_hasFPowerSeriesOnBall _ C hC (fun n =>
    (conjugate_norm_le_house σ _).trans (hhouse n i j))

end StrictEUnit
end
