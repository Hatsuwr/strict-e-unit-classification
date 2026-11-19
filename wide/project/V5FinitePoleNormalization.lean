import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Inv
import MeromorphicOriginRemoval

noncomputable section
open scoped Topology
open Filter
namespace StrictEUnit

/-- An entire numerator clearing a finite pole supplies actual meromorphy and
punctured differentiability; the arbitrary value of v at zero is irrelevant. -/
theorem v5_finite_pole_meromorphic {v F : ℂ → ℂ} (n : ℕ)
    (hF : Differentiable ℂ F) (hrep : ∀ z ≠ 0, F z = z^n * v z) :
    MeromorphicAt v 0 ∧ ∀ z ≠ 0, DifferentiableAt ℂ v z := by
  have he (z : ℂ) (hz : z ≠ 0) : F z / z^n = v z := by
    rw [hrep z hz]
    exact mul_div_cancel_left₀ _ (pow_ne_zero n hz)
  constructor
  · apply ((hF.analyticAt 0).meromorphicAt.div ((analyticAt_id.pow n).meromorphicAt)).congr
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact he z hz
  · intro z hz
    apply ((hF z).div (differentiableAt_id.pow n) (pow_ne_zero n hz)).congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hz] with w hw
    exact (he w hw).symm

/-- A reciprocal pair with a finite-pole entire numerator admits a genuine
entire, nowhere-zero normalized factor. Only v needs the finite-pole input. -/
theorem v5_finite_pole_inverse_pair_normalization {v u F : ℂ → ℂ} (n : ℕ)
    (hF : Differentiable ℂ F) (hrep : ∀ z ≠ 0, F z = z^n * v z)
    (hinv : ∀ z ≠ 0, v z * u z = 1) :
    ∃ q : ℤ, ∃ W : ℂ → ℂ, Differentiable ℂ W ∧ (∀ z, W z ≠ 0) ∧
      (∀ z ≠ 0, v z = z^q * W z) ∧
      Tendsto (fun x : ℝ => W (x : ℂ)) (𝓝[>] 0) (𝓝 (W 0)) ∧
      Tendsto (fun x : ℝ => deriv W (x : ℂ)) (𝓝[>] 0) (𝓝 (deriv W 0)) := by
  obtain ⟨hm, hd⟩ := v5_finite_pole_meromorphic n hF hrep
  have hnz (z : ℂ) (hz : z ≠ 0) : v z ≠ 0 := by
    intro hv
    have hh := hinv z hz
    rw [hv, zero_mul] at hh
    exact zero_ne_one hh
  obtain ⟨q, W, _, hW, hnW, _, he⟩ := exists_entire_nonzero_remove_origin hm hd hnz
  refine ⟨q, W, hW, hnW, he, ?_, ?_⟩
  · exact (hW.continuous.comp Complex.continuous_ofReal).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · have hD : Differentiable ℂ (deriv W) :=
      differentiableOn_univ.mp (hW.differentiableOn.deriv isOpen_univ)
    exact (hD.continuous.comp Complex.continuous_ofReal).continuousAt.tendsto.mono_left nhdsWithin_le_nhds

end StrictEUnit
#print axioms StrictEUnit.v5_finite_pole_meromorphic
#print axioms StrictEUnit.v5_finite_pole_inverse_pair_normalization
