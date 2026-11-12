import ArbitraryActualOrdinaryGerms
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.RingTheory.PowerSeries.Inverse

noncomputable section
open scoped Topology
namespace StrictEUnit

/-- The zeroth literal ordinary Taylor coefficient is the actual value. -/
theorem hasFPowerSeriesAt_ofScalars_value_zero
    (f : ℂ → ℂ) (P : PowerSeries ℂ)
    (hf : HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n P)) 0) :
    f 0=PowerSeries.constantCoeff ℂ P := by
  have h := hf.coeff_zero (fun _ => (1:ℂ))
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq,
    PowerSeries.coeff_zero_eq_constantCoeff,pow_zero,smul_eq_mul,mul_one] using h.symm

/-- The analytic inverse has exactly the formal inverse of the SAME ordinary
series. Existence and coefficient identification are proved here, with no
new convergence or representation premise. -/
theorem hasFPowerSeriesAt_inv_ofScalars
    (f : ℂ → ℂ) (P : PowerSeries ℂ)
    (hf : HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n P)) 0)
    (hP : PowerSeries.constantCoeff ℂ P ≠ 0) :
    HasFPowerSeriesAt (fun z => (f z)⁻¹)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n P⁻¹)) 0 := by
  have hf0 := hasFPowerSeriesAt_ofScalars_value_zero f P hf
  have hfn : f 0 ≠ 0 := by rw [hf0];exact hP
  obtain ⟨Q,hQ⟩ := analyticAt_has_ordinary_series (fun z => (f z)⁻¹)
    (hf.analyticAt.fun_inv hfn)
  have hm := hasFPowerSeriesAt_mul_ofScalars f (fun z => (f z)⁻¹) P Q hf hQ
  have hOne : HasFPowerSeriesAt (fun _ : ℂ => (1:ℂ))
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => PowerSeries.coeff ℂ n (1:PowerSeries ℂ))) 0 := by
    simpa only [Polynomial.eval_one,Polynomial.coe_one] using
      hasFPowerSeriesAt_polynomial_ofScalars (1:Polynomial ℂ)
  have hen := hf.analyticAt.continuousAt.eventually_ne hfn
  have hPQ : P*Q=1 := ordinary_series_eq_of_eventually _ _ _ _ hm hOne
    (hen.mono (fun z hz => mul_inv_cancel₀ hz))
  have hne : P ≠ 0 := by
    intro hz
    exact hP (by rw [hz,map_zero])
  have hQeq : Q=P⁻¹ := mul_left_cancel₀ hne
    (hPQ.trans (PowerSeries.mul_inv_cancel P hP).symm)
  rwa [hQeq] at hQ

/-- Literal quotient multiplication; the denominator is inverted only at
its nonzero constant, with the numerator's exact coefficients retained. -/
theorem hasFPowerSeriesAt_div_ofScalars
    (f g : ℂ → ℂ) (P Q : PowerSeries ℂ)
    (hf : HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n P)) 0)
    (hg : HasFPowerSeriesAt g
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n Q)) 0)
    (hQ : PowerSeries.constantCoeff ℂ Q ≠ 0) :
    HasFPowerSeriesAt (fun z => f z/g z)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n (P*Q⁻¹))) 0 := by
  simpa only [div_eq_mul_inv] using hasFPowerSeriesAt_mul_ofScalars f
    (fun z => (g z)⁻¹) P Q⁻¹ hf (hasFPowerSeriesAt_inv_ofScalars g Q hg hQ)

end StrictEUnit
end
