import EntireTaylorEmbedding
import ExponentialGeneratingGrowth

/-!
# Entire realization of a geometrically bounded factorial series

All analytic conclusions here are derived from the coefficient bound. Neither
analyticity nor a differential equation is an input. Zero coefficients and
identically zero series are allowed.
-/
noncomputable section
namespace StrictEUnit

/-- The literal factorial-normalized multilinear power series. -/
def stage41_factorialMultilinearSeries (a : ℕ → ℂ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (a n / (n.factorial : ℂ))

/-- Absolute convergence of the ordinary coefficients at every real radius. -/
theorem stage41_geometric_factorial_norm_summable (a : ℕ → ℂ) (C : ℝ)
    (ha : ∀ n, ‖a n‖ ≤ C ^ (n + 1)) (r : NNReal) :
    Summable (fun n => ‖a n / (n.factorial : ℂ)‖ * (r : ℝ) ^ n) := by
  have hs := (geometric_egf_summable a C ha ((r : ℝ) : ℂ)).norm
  convert hs using 1
  funext n
  simp only [norm_div, norm_mul, norm_pow, Complex.norm_natCast,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg r.coe_nonneg]
  ring

/-- The actual analytic power-series radius is infinite, not merely positive. -/
theorem stage41_factorialMultilinearSeries_radius (a : ℕ → ℂ) (C : ℝ)
    (ha : ∀ n, ‖a n‖ ≤ C ^ (n + 1)) :
    (stage41_factorialMultilinearSeries a).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  simpa only [stage41_factorialMultilinearSeries, ContinuousMultilinearMap.norm_mkPiRing]
    using stage41_geometric_factorial_norm_summable a C ha r

/-- The defined global sum has its literal power series on the entire plane. -/
theorem stage41_geometric_egf_hasFPowerSeriesOnBall (a : ℕ → ℂ) (C : ℝ)
    (ha : ∀ n, ‖a n‖ ≤ C ^ (n + 1)) :
    HasFPowerSeriesOnBall (exponentialGeneratingFunction a)
      (stage41_factorialMultilinearSeries a) 0 ⊤ := by
  refine ⟨by rw [stage41_factorialMultilinearSeries_radius a C ha], by simp, ?_⟩
  intro z _
  convert geometric_egf_hasSum a C ha z using 1
  · funext n
    simp only [stage41_factorialMultilinearSeries,
      ContinuousMultilinearMap.mkPiRing_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
    ring
  · simp

/-- Global analyticity follows from the coefficient bound alone. -/
theorem stage41_geometric_egf_analyticAt (a : ℕ → ℂ) (C : ℝ)
    (ha : ∀ n, ‖a n‖ ≤ C ^ (n + 1)) (z : ℂ) :
    AnalyticAt ℂ (exponentialGeneratingFunction a) z :=
  (stage41_geometric_egf_hasFPowerSeriesOnBall a C ha).analyticAt_of_mem (by simp)

/-- Entire complex differentiability is proved, not added as a premise. -/
theorem stage41_geometric_egf_differentiable (a : ℕ → ℂ) (C : ℝ)
    (ha : ∀ n, ‖a n‖ ≤ C ^ (n + 1)) :
    Differentiable ℂ (exponentialGeneratingFunction a) :=
  fun z => (stage41_geometric_egf_analyticAt a C ha z).differentiableAt

/-- The genuine Cauchy coefficient is exactly the source coefficient divided
by its factorial. -/
theorem stage41_geometric_egf_cauchyCoefficient (a : ℕ → ℂ) (C : ℝ)
    (ha : ∀ n, ‖a n‖ ≤ C ^ (n + 1)) (n : ℕ) :
    entireCauchyCoefficient (exponentialGeneratingFunction a) n =
      a n / (n.factorial : ℂ) := by
  apply entireCauchyCoefficient_eq_of_hasSum
    (stage41_geometric_egf_differentiable a C ha)
  intro z
  convert geometric_egf_hasSum a C ha z using 1
  funext j
  ring

/-- The entire Taylor map identifies the actual sum with the literal formal
power series. This equality is derived rather than a realization hypothesis. -/
theorem stage41_geometric_egf_formalTaylor (a : ℕ → ℂ) (C : ℝ)
    (ha : ∀ n, ‖a n‖ ≤ C ^ (n + 1)) :
    entireFormalTaylor (exponentialGeneratingFunction a) =
      PowerSeries.mk (fun n => a n / (n.factorial : ℂ)) := by
  ext n
  simpa only [coeff_entireFormalTaylor, PowerSeries.coeff_mk]
    using stage41_geometric_egf_cauchyCoefficient a C ha n

/-- Every normalized coefficient is also the actual iterated derivative at
zero, including the zeroth derivative. -/
theorem stage41_geometric_egf_iteratedDeriv_zero (a : ℕ → ℂ) (C : ℝ)
    (ha : ∀ n, ‖a n‖ ≤ C ^ (n + 1)) (n : ℕ) :
    iteratedDeriv n (exponentialGeneratingFunction a) 0 = a n := by
  rw [← entireCauchyCoefficient_factorial
    (stage41_geometric_egf_differentiable a C ha),
    stage41_geometric_egf_cauchyCoefficient a C ha]
  exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))

end StrictEUnit
