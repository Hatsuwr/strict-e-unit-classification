import EntirePolynomialGrowth
import Mathlib.Analysis.Calculus.SmoothSeries

/-! An actual global primitive obtained by integrating the Cauchy coefficients
of an entire function. Convergence and differentiation are proved. -/
noncomputable section
open scoped Topology BigOperators
open Complex Metric
namespace StrictEUnit

def entirePrimitive (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, (entireCauchyCoefficient f n / (n+1)) * z^(n+1)

lemma entireCauchyCoefficient_norm_summable {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (R : ℝ) (hR : 0 ≤ R) :
    Summable (fun n : ℕ => ‖entireCauchyCoefficient f n‖ * R^n) := by
  let p := cauchyPowerSeries f 0 1
  have htop : p.radius = ⊤ := top_le_iff.mp (hf.hasFPowerSeriesOnBall 0 (R := 1) (by norm_num)).r_le
  have hs := p.summable_norm_apply (x := (R:ℂ)) (by rw [htop]; simp)
  simpa [p, entireCauchyCoefficient, cauchyPowerSeries,
    ContinuousMultilinearMap.mkPiRing_apply, Fin.prod_const, smul_eq_mul,
    norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR,
    mul_comm] using hs

lemma hasDerivAt_entirePrimitive_term (f : ℂ → ℂ) (n : ℕ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => (entireCauchyCoefficient f n / (n+1))*w^(n+1))
      (entireCauchyCoefficient f n * z^n) z := by
  have hn : (n+1:ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  convert ((hasDerivAt_id z).pow (n+1)).const_mul (entireCauchyCoefficient f n / (n+1)) using 1
  simp only [Nat.add_sub_cancel, mul_one, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

/-- The series primitive has derivative f at every point of the complex plane. -/
theorem hasDerivAt_entirePrimitive {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ) :
    HasDerivAt (entirePrimitive f) (f z) z := by
  let R : ℝ := ‖z‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hs := entireCauchyCoefficient_norm_summable hf R hR.le
  have hh := hasDerivAt_tsum_of_isPreconnected hs isOpen_ball (convex_ball (0:ℂ) R).isPreconnected
    (fun n w _ => hasDerivAt_entirePrimitive_term f n w)
    (fun n w hw => show ‖entireCauchyCoefficient f n * w^n‖ ≤ ‖entireCauchyCoefficient f n‖ * R^n from by
      rw [norm_mul, norm_pow]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact pow_le_pow_left₀ (norm_nonneg _) (le_of_lt (by simpa [mem_ball_zero_iff] using hw)) n)
    (show (0:ℂ) ∈ ball 0 R from mem_ball_self hR)
    (show Summable (fun n : ℕ => (entireCauchyCoefficient f n / (n+1))*(0:ℂ)^(n+1)) by
      simpa using (summable_zero : Summable (fun _ : ℕ => (0:ℂ))))
    (show z ∈ ball (0:ℂ) R by simp [mem_ball_zero_iff, R])
  rw [(entireCauchyCoefficient_hasSum hf z).tsum_eq] at hh
  exact hh

@[simp] theorem entirePrimitive_zero (f : ℂ → ℂ) : entirePrimitive f 0 = 0 := by
  simp [entirePrimitive]

/-- Every entire function has a normalized entire primitive. -/
theorem exists_entire_primitive {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    ∃ g : ℂ → ℂ, g 0 = 0 ∧ Differentiable ℂ g ∧ ∀ z, HasDerivAt g (f z) z :=
  ⟨entirePrimitive f, entirePrimitive_zero f,
    fun z => (hasDerivAt_entirePrimitive hf z).differentiableAt,
    hasDerivAt_entirePrimitive hf⟩
end StrictEUnit
#print axioms StrictEUnit.entirePrimitive
#print axioms StrictEUnit.entireCauchyCoefficient_norm_summable
#print axioms StrictEUnit.hasDerivAt_entirePrimitive_term
#print axioms StrictEUnit.hasDerivAt_entirePrimitive
#print axioms StrictEUnit.entirePrimitive_zero
#print axioms StrictEUnit.exists_entire_primitive
