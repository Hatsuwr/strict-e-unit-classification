import V5LocalTaylorAlgebra
import EntireTaylorEmbedding
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

noncomputable section
open scoped Topology
open Filter
namespace StrictEUnit

theorem v5_log_analyticAt_one : AnalyticAt ℂ Complex.log 1 := by
  have hd : DifferentiableOn ℂ Complex.log Complex.slitPlane :=
    fun z hz => (Complex.differentiableAt_log hz).differentiableWithinAt
  exact hd.analyticAt (Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane)

def v5EntireLogPullback : entireFunctionAlgebra →ₐ[ℂ] v5LocalAnalyticAlgebra 1 where
  toFun f := ⟨fun z => f.val (Complex.log z), (f.property.analyticAt _).comp v5_log_analyticAt_one⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

def v5EntireLogTaylorAlgHom : entireFunctionAlgebra →ₐ[ℂ] PowerSeries ℂ :=
  (v5LocalTaylorAlgHom 1).comp v5EntireLogPullback

theorem v5EntireLogTaylorAlgHom_injective : Function.Injective v5EntireLogTaylorAlgHom := by
  intro f g h
  have he : (fun z => f.val (Complex.log z)) =ᶠ[𝓝 (1 : ℂ)]
      (fun z => g.val (Complex.log z)) :=
    (v5LocalTaylor_eq_iff_eventuallyEq (v5EntireLogPullback f).property
      (v5EntireLogPullback g).property).mp h
  have hfg : f.val =ᶠ[𝓝 (0 : ℂ)] g.val := by
    have hexp : Filter.Tendsto Complex.exp (𝓝 (0 : ℂ)) (𝓝 (1 : ℂ)) := by
      simpa only [ContinuousAt, Complex.exp_zero] using Complex.continuous_exp.continuousAt (x := (0 : ℂ))
    have hi : ∀ᶠ w in 𝓝 (0 : ℂ), Complex.log (Complex.exp w) = w := by
      have hm : (0 : ℂ) ∈ Complex.expPartialHomeomorph.source := by
        change -Real.pi < (0 : ℂ).im ∧ (0 : ℂ).im < Real.pi
        simp only [Complex.zero_im]
        constructor <;> linarith [Real.pi_pos]
      filter_upwards [Complex.expPartialHomeomorph.open_source.mem_nhds hm] with w hw
      exact Complex.expPartialHomeomorph.left_inv hw
    filter_upwards [hexp.eventually he, hi] with w hw hwi
    simpa only [hwi] using hw
  apply Subtype.ext
  exact AnalyticOnNhd.eq_of_eventuallyEq
    (fun z _ => f.property.analyticAt z) (fun z _ => g.property.analyticAt z) hfg

end StrictEUnit
#print axioms StrictEUnit.v5EntireLogTaylorAlgHom
#print axioms StrictEUnit.v5EntireLogTaylorAlgHom_injective
