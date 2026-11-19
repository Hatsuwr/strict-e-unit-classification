import V5MinimalRowProportional
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.Polynomial

namespace StrictEUnit
open scoped Topology BigOperators
open Filter

/-- A nonzero polynomial over the fixed coefficient field cannot vanish on an
open subset after embedding its coefficients in the complex numbers. -/
theorem v5_dense_polynomial_eval_ne_zero {K : Type*} [Field K] [Algebra K ℂ]
    (p : Polynomial K) (hp : p ≠ 0) :
    Dense {z : ℂ | (Polynomial.eval₂RingHom (algebraMap K ℂ) z) p ≠ 0} := by
  have hp' : p.map (algebraMap K ℂ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap K ℂ).injective).2 hp
  have h := dense_univ.diff_finite (Polynomial.finite_setOf_isRoot hp')
  simpa only [← Set.compl_eq_univ_diff, Set.compl_setOf, Polynomial.IsRoot.def,
    Polynomial.eval_map, Polynomial.coe_eval₂RingHom] using h

theorem v5_rowResidual_continuousAt {K : Type*} [Field K] [Algebra K ℂ]
    {u : ℂ → ℂ} {x : ℂ} (hu : AnalyticAt ℂ u x)
    (m : ℕ) (a : ℕ → Polynomial K) :
    ContinuousAt (v5RowResidual u m a) x := by
  unfold v5RowResidual
  apply tendsto_finset_sum
  intro j _
  exact ((a j).continuous_eval₂ (algebraMap K ℂ)).continuousAt.mul
    (by simpa only [iteratedDeriv_eq_iterate] using (hu.iterated_deriv j).continuousAt)

private theorem v5_continuous_residual_zero_of_eventual_mul_zero
    {K : Type*} [Field K] [Algebra K ℂ] (p : Polynomial K) (hp : p ≠ 0)
    {r : ℂ → ℂ} {x : ℂ} (hr : ContinuousAt r x)
    (h : ∀ᶠ z in 𝓝 x, (Polynomial.eval₂RingHom (algebraMap K ℂ) z) p * r z = 0) :
    r x = 0 := by
  have hd := v5_dense_polynomial_eval_ne_zero p hp
  have hf := mem_closure_iff_frequently.mp (hd x)
  refine tendsto_nhds_unique_of_frequently_eq hr tendsto_const_nhds ?_
  exact (hf.and_eventually h).mono fun z ⟨hnz, hz⟩ =>
    (mul_eq_zero.mp hz).resolve_left hnz

/-- Isolated zeros of a leading coefficient do not obstruct equivalence of
the two equations on holomorphic germs, even when the marked point is a zero. -/
theorem v5_minimal_rows_local_zero_iff {K : Type*} [Field K] [Algebra K ℂ]
    {f : ℂ → ℂ} {m : ℕ} (hsmall : ∀ n < m, ¬ v5HasAnnihilatorOrder K f n)
    (a b : ℕ → Polynomial K) (haTop : a m ≠ 0) (hbTop : b m ≠ 0)
    (ha : ∀ z, v5RowResidual f m a z = 0)
    (hb : ∀ z, v5RowResidual f m b z = 0)
    {u : ℂ → ℂ} {x : ℂ} (hu : AnalyticAt ℂ u x) :
    (∀ᶠ z in 𝓝 x, v5RowResidual u m a z = 0) ↔
      (∀ᶠ z in 𝓝 x, v5RowResidual u m b z = 0) := by
  have hs := v5_minimal_rows_scaled_residual hsmall a b ha hb u
  constructor
  · intro h
    filter_upwards [h.eventually_nhds, hu.eventually_analyticAt] with y hy huy
    refine v5_continuous_residual_zero_of_eventual_mul_zero (a m) haTop
      (v5_rowResidual_continuousAt huy m b) ?_
    filter_upwards [hy] with z hz
    rw [← hs z, hz, mul_zero]
  · intro h
    filter_upwards [h.eventually_nhds, hu.eventually_analyticAt] with y hy huy
    refine v5_continuous_residual_zero_of_eventual_mul_zero (b m) hbTop
      (v5_rowResidual_continuousAt huy m a) ?_
    filter_upwards [hy] with z hz
    rw [hs z, hz, mul_zero]

#print axioms v5_dense_polynomial_eval_ne_zero
#print axioms v5_rowResidual_continuousAt
#print axioms v5_minimal_rows_local_zero_iff
end StrictEUnit
