import V5RankOneRay
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Complex.CauchyIntegral

noncomputable section
open scoped Topology
open Filter
namespace StrictEUnit

/-- Removing the integer origin order changes the Euler coefficient by that integer. -/
theorem v5_normalized_euler_equation (u W b : ℂ → ℂ) (m : ℤ)
    (hW : Differentiable ℂ W)
    (hu : ∀ z ≠ 0, HasDerivAt u (b z * u z / z) z)
    (he : ∀ z ≠ 0, u z = z^m * W z) :
    ∀ z ≠ 0, z * deriv W z = (b z - (m : ℂ)) * W z := by
  intro z hz
  have hp := (hasDerivAt_zpow m z (Or.inl hz)).mul (hW z).hasDerivAt
  have hp' : HasDerivAt u ((m : ℂ)*z^(m-1)*W z + z^m * deriv W z) z := by
    apply hp.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hz] with w hw
    exact he w hw
  have hh := (hu z hz).unique hp'
  rw [he z hz] at hh
  have hpow : z^(m-1) * z = z^m := by
    calc
      _ = z^(m-1) * z^(1 : ℤ) := by rw [zpow_one]
      _ = z^m := by rw [← zpow_add₀ hz]; congr 1; ring
  have hmul := congrArg (fun a : ℂ => a*z) hh
  dsimp only at hmul
  rw [div_mul_cancel₀ _ hz] at hmul
  have hh' : z^m * (z * deriv W z) = z^m * ((b z - (m : ℂ))*W z) := by
    calc
      _ = ( (m : ℂ)*z^(m-1)*W z + z^m * deriv W z)*z -
          (m : ℂ) * (z^(m-1)*z) * W z := by ring
      _ = b z * (z^m * W z) - (m : ℂ) * z^m * W z := by rw [← hmul, hpow]
      _ = _ := by ring
  exact mul_left_cancel₀ (zpow_ne_zero _ hz) hh'

/-- The normalized entire nonzero factor forces b to have right limit m. -/
theorem v5_normalized_euler_coefficient_limit (u W b : ℂ → ℂ) (m : ℤ)
    (hW : Differentiable ℂ W) (hW0 : W 0 ≠ 0)
    (hu : ∀ z ≠ 0, HasDerivAt u (b z * u z / z) z)
    (he : ∀ z ≠ 0, u z = z^m * W z) :
    Tendsto (fun x : ℝ => b (x : ℂ)) (𝓝[>] 0) (𝓝 (m : ℂ)) := by
  have hD : Differentiable ℂ (deriv W) :=
    differentiableOn_univ.mp (hW.differentiableOn.deriv isOpen_univ)
  apply v5_normalized_rank_one_coefficient_limit (fun x : ℝ => W x)
    (fun x : ℝ => deriv W x) (fun x : ℝ => b x) (m : ℂ) (W 0) (deriv W 0) hW0
  · exact (hW.continuous.comp Complex.continuous_ofReal).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · exact (hD.continuous.comp Complex.continuous_ofReal).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx : x ≠ 0)
    exact v5_normalized_euler_equation u W b m hW hu he x hx0

end StrictEUnit
#print axioms StrictEUnit.v5_normalized_euler_equation
#print axioms StrictEUnit.v5_normalized_euler_coefficient_limit
