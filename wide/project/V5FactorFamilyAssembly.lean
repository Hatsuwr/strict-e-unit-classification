import V5OrdinaryScalarUniqueness

namespace StrictEUnit
open scoped Topology BigOperators
open Filter

private theorem v5_weightedGerm_analyticAt {n : ℕ} {u : Fin n → ℂ → ℂ} {z : ℂ}
    (hu : ∀ j, AnalyticAt ℂ (u j) z) (c : Fin n → ℂ) :
    AnalyticAt ℂ (v5WeightedGerm u c) z := by
  unfold v5WeightedGerm
  exact Finset.analyticAt_sum _ fun j _ => analyticAt_const.mul (hu j)

/-- Extract an order-sized analytic family for the cleared right row. The
left-row assumption applies to the *rational* images, obtained by dividing
the cleared right residuals by the common denominator. Regularity of the
left row and nonvanishing of that denominator are needed only at y. -/
theorem v5_extract_right_factor_family {K L : Type*} [Field K] [Algebra K ℂ]
    [Field L] [Algebra L ℂ] {n m : ℕ} (hm : m ≤ n)
    {x y : ℂ} {D : Set ℂ} (hD : IsPreconnected D) (hx : D ∈ 𝓝 x) (hy : y ∈ D)
    (u : Fin n → ℂ → ℂ) (hu : ∀ j, AnalyticOnNhd ℂ (u j) D)
    (hind : v5FiniteGermIndependent x u)
    (q : ℕ → Polynomial K) (d : ℂ → ℂ) (hd : AnalyticAt ℂ d y) (hdy : d y ≠ 0)
    (r : ℕ → Polynomial L) (hr : (r (n-m)).eval₂ (algebraMap L ℂ) y ≠ 0)
    (hleft : ∀ j, ∀ᶠ z in 𝓝 y,
      v5RowResidual (fun w => v5RowResidual (u j) m q w / d w) (n-m) r z = 0) :
    ∃ v : Fin m → ℂ → ℂ, v5FiniteGermIndependent x v ∧
      ∀ i, AnalyticOnNhd ℂ (v i) D ∧
        ∀ᶠ z in 𝓝 x, v5RowResidual (v i) m q z = 0 := by
  classical
  let image (j : Fin n) (z : ℂ) := v5RowResidual (u j) m q z / d z
  have ha (j : Fin n) : AnalyticAt ℂ (image j) y :=
    (v5_rowResidual_analyticAt (hu j y hy) m q).div hd hdy
  obtain ⟨a, hai, haj⟩ := v5_exists_independent_initialJet_kernel hm
    (v5FactorInitialJetMap (n-m) image y)
  refine ⟨fun i => v5WeightedGerm u (a i), v5_weighted_germs_independent hind hai, ?_⟩
  intro i
  let c := a i
  have hv : AnalyticOnNhd ℂ (v5WeightedGerm u c) D :=
    fun z hz => v5_weightedGerm_analyticAt (fun j => hu j z hz) c
  refine ⟨hv, v5_rowResidual_eventually_zero_at_mark hD hx hy hv m q ?_⟩
  have hall : ∀ᶠ z in 𝓝 y, ∀ j, AnalyticAt ℂ (image j) z ∧
      v5RowResidual (image j) (n-m) r z = 0 :=
    Filter.eventually_all.mpr (fun j => (ha j).eventually_analyticAt.and (hleft j))
  have hres : ∀ᶠ z in 𝓝 y, v5RowResidual (v5WeightedGerm image c) (n-m) r z = 0 := by
    filter_upwards [hall] with z hz
    rw [v5_rowResidual_weightedGerm (fun j => (hz j).1)]
    simp [v5WeightedGerm, fun j => (hz j).2]
  have hzero := v5_cleared_scalar_zero_of_zero_jets r hr
    (v5_weightedGerm_analyticAt ha c) hres ((v5_initialJetMap_eq_zero_iff ha c).mp (haj i))
  have hU : ∀ᶠ z in 𝓝 y, ∀ j, AnalyticAt ℂ (u j) z :=
    Filter.eventually_all.mpr (fun j => (hu j y hy).eventually_analyticAt)
  have hdn : ∀ᶠ z in 𝓝 y, d z ≠ 0 := hd.continuousAt.eventually_ne hdy
  filter_upwards [hzero, hU, hdn] with z hz hu' hd'
  rw [v5_rowResidual_weightedGerm hu']
  have hdiv : v5WeightedGerm image c z =
      v5WeightedGerm (fun j w => v5RowResidual (u j) m q w) c z / d z := by
    simp only [v5WeightedGerm, image, Finset.sum_div, mul_div_assoc]
  change v5WeightedGerm image c z = 0 at hz
  rw [hdiv] at hz
  exact (div_eq_zero_iff.mp hz).resolve_right hd'

#print axioms v5_extract_right_factor_family
end StrictEUnit
