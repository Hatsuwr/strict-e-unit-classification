import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section
open scoped Topology
namespace StrictEUnit
variable {E : Type*} [NormedRing E] [NormedAlgebra ℂ E]

/-- Undoing the exponential change of independent variable on the principal slit plane. -/
theorem v5_log_pullback_hasDerivAt (A U : ℂ → E)
    (hU : ∀ w, HasDerivAt U (Complex.exp w • (A (Complex.exp w) * U w)) w)
    {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasDerivAt (fun z => U (Complex.log z)) (A z * U (Complex.log z)) z := by
  have h := (hU (Complex.log z)).scomp z (Complex.hasDerivAt_log hz)
  simpa only [Complex.exp_log (Complex.slitPlane_ne_zero hz), smul_smul,
    inv_mul_cancel₀ (Complex.slitPlane_ne_zero hz), one_smul, Function.comp_def] using h

/-- Entire differentiability plus the usual derivative equation is sufficient. -/
theorem v5_log_pullback_of_deriv (A U : ℂ → E) (hU : Differentiable ℂ U)
    (hode : ∀ w, deriv U w = Complex.exp w • (A (Complex.exp w) * U w))
    {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasDerivAt (fun z => U (Complex.log z)) (A z * U (Complex.log z)) z := by
  apply v5_log_pullback_hasDerivAt A U _ hz
  intro w
  simpa only [hode w] using (hU w).hasDerivAt

omit [NormedRing E] [NormedAlgebra ℂ E] in
/-- The logarithmic pullback preserves the original marked initial value. -/
theorem v5_log_pullback_mark (U : ℂ → E) : U (Complex.log 1) = U 0 := by
  rw [Complex.log_one]

/-- A neighborhood of 1 carries the original ODE and the initial mark. -/
theorem v5_log_pullback_local_marked (A U : ℂ → E) (hU : Differentiable ℂ U)
    (hode : ∀ w, deriv U w = Complex.exp w • (A (Complex.exp w) * U w)) :
    (∀ᶠ z in 𝓝 (1 : ℂ),
      HasDerivAt (fun z => U (Complex.log z)) (A z * U (Complex.log z)) z) ∧
    U (Complex.log 1) = U 0 := by
  refine ⟨?_, v5_log_pullback_mark U⟩
  filter_upwards [Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane] with z hz
  exact v5_log_pullback_of_deriv A U hU hode hz

end StrictEUnit
#print axioms StrictEUnit.v5_log_pullback_hasDerivAt
#print axioms StrictEUnit.v5_log_pullback_of_deriv
#print axioms StrictEUnit.v5_log_pullback_mark
#print axioms StrictEUnit.v5_log_pullback_local_marked
