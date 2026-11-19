import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic

/-!
New reconstruction, not recovered original source.
A locally bounded meromorphic function has a globally analytic normal form.
The continuous majorant is an ordinary estimate, and is later constructed
explicitly from the coefficients of the given monic relation.
-/
noncomputable section
open scoped Topology
open Filter Set

namespace StrictEUnit

/-- A continuous majorant excludes negative meromorphic order at each point. -/
theorem meromorphic_order_nonneg_of_continuous_envelope {f : ℂ → ℂ} {B : ℂ → ℝ}
    (hf : MeromorphicOn f Set.univ) (hB : Continuous B)
    (hbound : ∀ z, ‖f z‖ ≤ B z) (x : ℂ) : 0 ≤ (hf x (Set.mem_univ x)).order := by
  by_contra hn
  have hn' : (hf x (Set.mem_univ x)).order < 0 := lt_of_not_ge hn
  have ht : Tendsto (fun z => ‖f z‖) (𝓝[≠] x) atTop :=
    tendsto_norm_atTop_iff_cobounded.mpr
      ((hf x (Set.mem_univ x)).tendsto_cobounded_of_order_neg hn')
  have he₁ : ∀ᶠ z in 𝓝[≠] x, B x + 1 < ‖f z‖ :=
    ht.eventually_gt_atTop (B x + 1)
  have he₂ : ∀ᶠ z in 𝓝[≠] x, B z < B x + 1 :=
    Filter.Tendsto.eventually_lt_const (by linarith)
      hB.continuousAt.continuousWithinAt.tendsto
  obtain ⟨z, hz₁, hz₂⟩ := (he₁.and he₂).exists
  exact (not_lt_of_ge (hbound z)) (hz₂.trans hz₁)

/-- Normalize a bounded meromorphic function and retain its continuous majorant.
The representative agrees with the original in every punctured neighborhood. -/
theorem exists_entire_of_meromorphic_continuous_envelope {f : ℂ → ℂ} {B : ℂ → ℝ}
    (hf : MeromorphicOn f Set.univ) (hB : Continuous B)
    (hbound : ∀ z, ‖f z‖ ≤ B z) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
      (∀ x, H =ᶠ[𝓝[≠] x] f) ∧ (∀ x, ‖H x‖ ≤ B x) := by
  let H : ℂ → ℂ := toMeromorphicNFOn f Set.univ
  have hNF : MeromorphicNFOn H Set.univ :=
    meromorphicNFOn_toMeromorphicNFOn f Set.univ
  have hHa : ∀ x, AnalyticAt ℂ H x := by
    intro x
    apply (hNF (Set.mem_univ x)).order_nonneg_iff_analyticAt.mp
    change 0 ≤ ((meromorphicNFOn_toMeromorphicNFOn f Set.univ)
      (Set.mem_univ x)).meromorphicAt.order
    rw [order_toMeromorphicNFOn hf (Set.mem_univ x)]
    exact meromorphic_order_nonneg_of_continuous_envelope hf hB hbound x
  have hHeq : ∀ x, H =ᶠ[𝓝[≠] x] f := fun x =>
    hf.toMeromorphicNFOn_eq_self_on_nhdNE (Set.mem_univ x)
  refine ⟨H, fun x => (hHa x).differentiableAt, hHeq, ?_⟩
  intro x
  apply le_of_tendsto_of_tendsto (b := 𝓝[≠] x)
    (hHa x).continuousAt.continuousWithinAt.tendsto.norm
    hB.continuousAt.continuousWithinAt.tendsto
  filter_upwards [hHeq x] with z hz
  simpa only [hz] using hbound z

/-- At every point where the original representative is continuous, normalization
has the same value. -/
theorem entire_representative_eq_of_continuousAt {f H : ℂ → ℂ}
    (hH : Differentiable ℂ H) (heq : ∀ x, H =ᶠ[𝓝[≠] x] f)
    {x : ℂ} (hf : ContinuousAt f x) : H x = f x := by
  exact (((hH x).continuousAt.eventuallyEq_nhd_iff_eventuallyEq_nhdNE hf).mp
    (heq x)).eq_of_nhds

end StrictEUnit

#print axioms StrictEUnit.meromorphic_order_nonneg_of_continuous_envelope
#print axioms StrictEUnit.exists_entire_of_meromorphic_continuous_envelope
#print axioms StrictEUnit.entire_representative_eq_of_continuousAt
