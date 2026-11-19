import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.RingTheory.PowerSeries.Derivative

noncomputable section
open scoped Topology
namespace StrictEUnit

/-- Genuine scalar Taylor series at an arbitrary center, in the displacement variable. -/
def v5LocalTaylor (f : ℂ → ℂ) (c : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun n => iteratedDeriv n f c / (n.factorial : ℂ))

@[simp] theorem v5LocalTaylor_coeff (f : ℂ → ℂ) (c : ℂ) (n : ℕ) :
    PowerSeries.coeff ℂ n (v5LocalTaylor f c) = iteratedDeriv n f c / (n.factorial : ℂ) := by
  simp [v5LocalTaylor]

@[simp] theorem v5LocalTaylor_constantCoeff (f : ℂ → ℂ) (c : ℂ) :
    PowerSeries.constantCoeff ℂ (v5LocalTaylor f c) = f c := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp

/-- This formal series really converges to the original analytic germ. -/
theorem v5LocalTaylor_hasFPowerSeriesAt {f : ℂ → ℂ} {c : ℂ} (hf : AnalyticAt ℂ f c) :
    HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n (v5LocalTaylor f c))) c := by
  simpa only [v5LocalTaylor_coeff] using hf.hasFPowerSeriesAt

/-- Equality of Taylor series recovers equality on a neighborhood, not global equality. -/
theorem v5LocalTaylor_eq_iff_eventuallyEq {f g : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) (hg : AnalyticAt ℂ g c) :
    v5LocalTaylor f c = v5LocalTaylor g c ↔ f =ᶠ[𝓝 c] g := by
  constructor
  · intro he
    have hf' := v5LocalTaylor_hasFPowerSeriesAt hf
    rw [he] at hf'
    filter_upwards [hf'.eventually_hasSum_sub,
      (v5LocalTaylor_hasFPowerSeriesAt hg).eventually_hasSum_sub] with z hz hz'
    exact hz.unique hz'
  · intro he
    have hh := (v5LocalTaylor_hasFPowerSeriesAt hf).eq_formalMultilinearSeries_of_eventually
      (v5LocalTaylor_hasFPowerSeriesAt hg) he
    ext n
    have hn := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) hh
    simpa using hn

/-- Differentiation commutes with the local Taylor construction. -/
theorem v5LocalTaylor_deriv (f : ℂ → ℂ) (c : ℂ) :
    v5LocalTaylor (deriv f) c = PowerSeries.derivative ℂ (v5LocalTaylor f c) := by
  ext n
  simp only [v5LocalTaylor_coeff, PowerSeries.coeff_derivative]
  rw [← iteratedDeriv_succ', Nat.factorial_succ, Nat.cast_mul]
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn1 : ((n+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast at hn1 ⊢
  field_simp
  ring

theorem v5LocalTaylor_add {f g : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) (hg : AnalyticAt ℂ g c) :
    v5LocalTaylor (fun z => f z + g z) c = v5LocalTaylor f c + v5LocalTaylor g c := by
  ext n
  simp only [v5LocalTaylor_coeff, map_add]
  change iteratedDeriv n (f + g) c / _ = _
  rw [iteratedDeriv_add (hf.contDiffAt : ContDiffAt ℂ n f c)
    (hg.contDiffAt : ContDiffAt ℂ n g c), add_div]

end StrictEUnit
#print axioms StrictEUnit.v5LocalTaylor_constantCoeff
#print axioms StrictEUnit.v5LocalTaylor_hasFPowerSeriesAt
#print axioms StrictEUnit.v5LocalTaylor_eq_iff_eventuallyEq
#print axioms StrictEUnit.v5LocalTaylor_deriv

#print axioms StrictEUnit.v5LocalTaylor_add
