import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Localization.Integral

/-! New reconstruction, not recovered historical source.
Clearing the coefficients of an algebraic relation can be done using the
existing localization-integrality theorem, before any analytic reasoning. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped nonZeroDivisors
namespace StrictEUnit

/-- An algebraic Laurent element over k(t) has a nonzero polynomial multiple
integral over k[t]. In particular that multiple satisfies a monic relation
whose coefficients are actual polynomials, not rational functions. -/
theorem integral_laurent_exists_polynomial_multiple
    {k : Type*} [Field k] {x : LaurentSeries k} (hx : IsIntegral (RatFunc k) x) :
    ∃ q : Polynomial k, q ≠ 0 ∧
      IsIntegral (Polynomial k) (algebraMap (Polynomial k) (LaurentSeries k) q * x) := by
  obtain ⟨q, hq⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (Rₘ := RatFunc k) (nonZeroDivisors (Polynomial k)) x hx
  refine ⟨q, nonZeroDivisors.coe_ne_zero q, ?_⟩
  simpa only [Submonoid.smul_def, Algebra.smul_def] using hq

end StrictEUnit
