import ConvergentOrdinaryGerms
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

noncomputable section
open scoped Topology
namespace StrictEUnit

theorem hasFPowerSeriesOnBall_deriv_ofScalars
    (f : ℂ → ℂ) (P : PowerSeries ℂ) (R : ENNReal)
    (h : HasFPowerSeriesOnBall f
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n P)) 0 R) :
    HasFPowerSeriesOnBall (deriv f)
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => PowerSeries.coeff ℂ n (PowerSeries.derivative ℂ P))) 0 R := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n P)
  let ev : (ℂ →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ (1:ℂ)
  have hp : HasFPowerSeriesOnBall f p 0 R := h
  have hcoeff (n : ℕ) :
      (ev.compFormalMultilinearSeries p.derivSeries).coeff n =
        PowerSeries.coeff ℂ n (PowerSeries.derivative ℂ P) := by
    change p.derivSeries.coeff n (1:ℂ) = _
    rw [FormalMultilinearSeries.derivSeries_coeff_one,
      FormalMultilinearSeries.coeff_ofScalars, PowerSeries.coeff_derivative]
    simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring
  have hseries : ev.compFormalMultilinearSeries p.derivSeries =
      FormalMultilinearSeries.ofScalars ℂ
        (fun n => PowerSeries.coeff ℂ n (PowerSeries.derivative ℂ P)) := by
    ext n u
    simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
      hcoeff, FormalMultilinearSeries.coeff_ofScalars]
  have hd := ev.comp_hasFPowerSeriesOnBall hp.fderiv
  rw [hseries] at hd
  exact hd

theorem hasFPowerSeriesAt_deriv_ofScalars
    (f : ℂ → ℂ) (P : PowerSeries ℂ)
    (h : HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n P)) 0) :
    HasFPowerSeriesAt (deriv f)
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => PowerSeries.coeff ℂ n (PowerSeries.derivative ℂ P))) 0 := by
  obtain ⟨R,hR⟩ := h
  exact ⟨R,hasFPowerSeriesOnBall_deriv_ofScalars f P R hR⟩

theorem ordinaryGerm_iteratedDeriv_zero
    (a : ℕ → ℂ) (C : ℝ) (hC : 1 ≤ C) (ha : ∀ n, ‖a n‖ ≤ C^n) (n : ℕ) :
    iteratedDeriv n (ordinaryGermSum a) 0 = (n.factorial:ℂ) * a n := by
  have h := (ordinaryGerm_hasFPowerSeriesOnBall a C hC ha).factorial_smul (y := (1:ℂ)) n
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq, one_pow, mul_one,
    smul_eq_mul, nsmul_eq_mul, iteratedDeriv_eq_iteratedFDeriv] using h.symm

end StrictEUnit
end
