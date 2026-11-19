import V5LocalTaylor
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.RingTheory.Adjoin.Basic

noncomputable section
open scoped Topology BigOperators
open Filter
namespace StrictEUnit

theorem v5LocalTaylor_eq_of_series {f : ℂ → ℂ} {c : ℂ} (hf : AnalyticAt ℂ f c)
    (P : PowerSeries ℂ)
    (hP : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ
      (fun n => PowerSeries.coeff ℂ n P)) c) : v5LocalTaylor f c = P := by
  have hh := (v5LocalTaylor_hasFPowerSeriesAt hf).eq_formalMultilinearSeries hP
  ext n
  simpa using congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) hh

theorem v5LocalTaylor_eventually_summable_norm {f : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) :
    ∀ᶠ z in 𝓝 (0 : ℂ), Summable (fun n => ‖PowerSeries.coeff ℂ n (v5LocalTaylor f c) * z^n‖) := by
  let p := FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n (v5LocalTaylor f c))
  obtain ⟨r, hr⟩ := v5LocalTaylor_hasFPowerSeriesAt hf
  filter_upwards [EMetric.ball_mem_nhds (0 : ℂ) hr.r_pos] with z hz
  have hh := p.summable_norm_apply (EMetric.ball_subset_ball hr.r_le hz)
  simpa [p, FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul, mul_comm] using hh

theorem v5LocalTaylor_mul {f g : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) (hg : AnalyticAt ℂ g c) :
    v5LocalTaylor (fun z => f z * g z) c = v5LocalTaylor f c * v5LocalTaylor g c := by
  apply v5LocalTaylor_eq_of_series (hf.mul hg)
  apply hasFPowerSeriesAt_iff.mpr
  filter_upwards [(hasFPowerSeriesAt_iff.mp (v5LocalTaylor_hasFPowerSeriesAt hf)),
    (hasFPowerSeriesAt_iff.mp (v5LocalTaylor_hasFPowerSeriesAt hg)),
    v5LocalTaylor_eventually_summable_norm hf, v5LocalTaylor_eventually_summable_norm hg]
    with z hfs hgs hfn hgn
  simp only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul] at hfs hgs ⊢
  have hs := (summable_norm_sum_mul_antidiagonal_of_summable_norm hfn hgn).of_norm.hasSum
  rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hgn] at hs
  have hfs' : HasSum (fun n => PowerSeries.coeff ℂ n (v5LocalTaylor f c) * z^n) (f (c+z)) := by
    simpa [mul_comm] using hfs
  have hgs' : HasSum (fun n => PowerSeries.coeff ℂ n (v5LocalTaylor g c) * z^n) (g (c+z)) := by
    simpa [mul_comm] using hgs
  rw [hfs'.tsum_eq, hgs'.tsum_eq] at hs
  convert hs using 1
  funext n
  rw [PowerSeries.coeff_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [← Finset.mem_antidiagonal.mp hij, pow_add]
  ring

theorem v5LocalTaylor_const (a c : ℂ) :
    v5LocalTaylor (fun _ => a) c = PowerSeries.C ℂ a := by
  apply v5LocalTaylor_eq_of_series analyticAt_const
  apply hasFPowerSeriesAt_iff.mpr
  apply Filter.Eventually.of_forall
  intro z
  simp only [FormalMultilinearSeries.coeff_ofScalars, PowerSeries.coeff_C]
  convert (hasSum_ite_eq (0 : ℕ) a) using 1
  funext n
  by_cases hn : n = 0 <;> simp [hn]

/-- Actual functions analytic near c; equality here remains global function equality. -/
def v5LocalAnalyticAlgebra (c : ℂ) : Subalgebra ℂ (ℂ → ℂ) where
  carrier := {f | AnalyticAt ℂ f c}
  zero_mem' := analyticAt_const
  one_mem' := analyticAt_const
  add_mem' := fun hf hg => hf.add hg
  mul_mem' := fun hf hg => hf.mul hg
  algebraMap_mem' := fun _ => analyticAt_const

def v5LocalTaylorAlgHom (c : ℂ) : v5LocalAnalyticAlgebra c →ₐ[ℂ] PowerSeries ℂ where
  toFun f := v5LocalTaylor f.val c
  map_zero' := by simpa using v5LocalTaylor_const 0 c
  map_one' := by simpa using v5LocalTaylor_const 1 c
  map_add' f g := v5LocalTaylor_add f.property g.property
  map_mul' f g := v5LocalTaylor_mul f.property g.property
  commutes' a := v5LocalTaylor_const a c

end StrictEUnit
#print axioms StrictEUnit.v5LocalTaylor_mul
#print axioms StrictEUnit.v5LocalTaylor_const
#print axioms StrictEUnit.v5LocalTaylorAlgHom
