import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.TaylorSeries
import GrowthCutoff

/-! Actual entire-function reconstruction from modulus growth.
This does not replace a real-part estimate by a modulus estimate: converting
the manuscript's real-part bound remains a separate analytic step. -/
noncomputable section
open scoped Topology BigOperators
open Complex Metric
namespace StrictEUnit

def entireCauchyCoefficient (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  cauchyPowerSeries f 0 1 n (fun _ => 1)

lemma entireCauchyCoefficient_radius {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {r : ℝ} (hr : 0 < r) (n : ℕ) :
    entireCauchyCoefficient f n = cauchyPowerSeries f 0 r n (fun _ => 1) := by
  have he := (hf.hasFPowerSeriesOnBall 0 (R := 1) (by norm_num)).hasFPowerSeriesAt.eq_formalMultilinearSeries
    (hf.hasFPowerSeriesOnBall 0 (R := ⟨r,hr.le⟩) hr).hasFPowerSeriesAt
  exact congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p n (fun _ => 1)) he

/-- A Cauchy coefficient estimate derived from actual complex differentiability. -/
theorem norm_entireCauchyCoefficient_le {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {r C : ℝ} (hr : 0 < r) (hC : ∀ z : ℂ, ‖z‖ = r → ‖f z‖ ≤ C) (n : ℕ) :
    ‖entireCauchyCoefficient f n‖ ≤ C / r ^ n := by
  rw [entireCauchyCoefficient_radius hf hr, cauchyPowerSeries_apply]
  have hh := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (f := fun z : ℂ => (1 / (z - 0)) ^ n • (z - 0)⁻¹ • f z)
    (c := 0) (R := r) (C := r⁻¹ ^ n * r⁻¹ * C) hr.le
  have hb : ∀ z ∈ sphere (0:ℂ) r,
      ‖(1 / (z - 0)) ^ n • (z - 0)⁻¹ • f z‖ ≤ r⁻¹ ^ n * r⁻¹ * C := by
    intro z hz
    have hz' : ‖z‖ = r := by simpa [mem_sphere, dist_zero_right] using hz
    simp only [sub_zero, norm_smul, norm_pow, norm_div, norm_one, norm_inv, hz', one_div]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hC z hz') (mul_nonneg (pow_nonneg (inv_nonneg.mpr hr.le) _) (inv_nonneg.mpr hr.le))
  convert hh hb using 1; field_simp; ring

lemma entireCauchyCoefficient_hasSum {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ) :
    HasSum (fun n : ℕ => entireCauchyCoefficient f n * z ^ n) (f z) := by
  have h := (hf.hasFPowerSeriesOnBall 0 (R := 1) (by norm_num)).hasSum
    (y := z) (by simp)
  simpa [entireCauchyCoefficient, cauchyPowerSeries,
    ContinuousMultilinearMap.mkPiRing_apply, Fin.prod_const, smul_eq_mul, mul_comm] using h

/-- Polynomial modulus growth, with the stated logarithmic correction, forces
an actual entire function (not merely a formal coefficient sequence) to be polynomial. -/
theorem entire_polynomial_of_modulus_growth {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (C M : ℝ) (N : ℕ)
    (hg : ∀ z : ℂ, 1 ≤ ‖z‖ → ‖f z‖ ≤ C * ‖z‖ ^ N + M * Real.log ‖z‖ + C) :
    ∃ P : Polynomial ℂ, (∀ z : ℂ, P.eval z = f z) ∧ P.natDegree ≤ N := by
  classical
  have hz : ∀ j : ℕ, N < j → entireCauchyCoefficient f j = 0 := by
    intro j hj
    apply coefficient_eq_zero_of_fourier_bound _ C M hj
    intro r hr
    have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
    have hbound : ∀ z : ℂ, ‖z‖ = r → ‖f z‖ ≤ C * r ^ N + M * Real.log r + C := by
      intro z he
      simpa [he] using hg z (by simpa [he] using hr)
    have hnonneg : 0 ≤ C * r ^ N + M * Real.log r + C :=
      (norm_nonneg (f (r:ℂ))).trans (hbound (r:ℂ) (by simp [Real.norm_eq_abs, abs_of_pos hr0]))
    exact (norm_entireCauchyCoefficient_le hf hr0 hbound j).trans
      (div_le_div_of_nonneg_right (by linarith) (pow_nonneg hr0.le _))
  let P : Polynomial ℂ := ∑ n ∈ Finset.range (N+1), Polynomial.monomial n (entireCauchyCoefficient f n)
  refine ⟨P, ?_, ?_⟩
  · intro z
    have hs := entireCauchyCoefficient_hasSum hf z
    have he : ∑ n ∈ Finset.range (N+1), entireCauchyCoefficient f n * z^n = f z :=
      (hasSum_sum_of_ne_finset_zero (fun n hn => by
        have hnj : N < n := by
          have hn' : ¬ n < N+1 := by simpa only [Finset.mem_range] using hn
          omega
        simp [hz n hnj])).unique hs
    simpa [P, Polynomial.eval_finset_sum, Polynomial.eval_monomial] using he
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro n hn
    exact (Polynomial.natDegree_monomial_le _).trans (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hn))
end StrictEUnit
#print axioms StrictEUnit.entireCauchyCoefficient
#print axioms StrictEUnit.entireCauchyCoefficient_radius
#print axioms StrictEUnit.norm_entireCauchyCoefficient_le
#print axioms StrictEUnit.entireCauchyCoefficient_hasSum
#print axioms StrictEUnit.entire_polynomial_of_modulus_growth
