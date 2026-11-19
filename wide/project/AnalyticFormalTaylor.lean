import Mathlib.Analysis.Calculus.Deriv.Polynomial
import EntirePrimitive
import FormalPowerSeriesArithmetic
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! Actual entire Taylor coefficients define a formal series compatible with
multiplication and differentiation. No formal ODE is supplied as an input. -/
noncomputable section
open scoped Topology BigOperators
open Complex
namespace StrictEUnit

def entireFormalTaylor (f : ℂ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (entireCauchyCoefficient f)

@[simp] lemma coeff_entireFormalTaylor (f : ℂ → ℂ) (n : ℕ) :
    PowerSeries.coeff ℂ n (entireFormalTaylor f) = entireCauchyCoefficient f n := by
  simp [entireFormalTaylor]

lemma entireCauchyCoefficient_eq_of_hasSum {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (a : ℕ → ℂ) (ha : ∀ z : ℂ, HasSum (fun n => a n * z^n) (f z)) (n : ℕ) :
    entireCauchyCoefficient f n = a n := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ := fun m =>
    ContinuousMultilinearMap.mkPiRing ℂ (Fin m) (a m)
  have hp : HasFPowerSeriesAt f p 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    apply Filter.Eventually.of_forall
    intro z
    simpa [p, FormalMultilinearSeries.coeff, ContinuousMultilinearMap.mkPiRing_apply,
      smul_eq_mul, mul_comm] using ha z
  have he := (hf.hasFPowerSeriesOnBall 0 (R := 1) (by norm_num)).hasFPowerSeriesAt.eq_formalMultilinearSeries hp
  have he' := congrArg (fun s : FormalMultilinearSeries ℂ ℂ ℂ => s n (fun _ => 1)) he
  simpa [entireCauchyCoefficient, p, ContinuousMultilinearMap.mkPiRing_apply] using he'

lemma entireCauchyCoefficient_factorial {f : ℂ → ℂ} (hf : Differentiable ℂ f) (n : ℕ) :
    (n.factorial : ℂ) * entireCauchyCoefficient f n = iteratedDeriv n f 0 := by
  have hh := (hf.hasFPowerSeriesOnBall 0 (R := 1) (by norm_num)).factorial_smul (y := (1:ℂ)) n
  simpa [entireCauchyCoefficient, iteratedDeriv_eq_iteratedFDeriv, nsmul_eq_mul] using hh

lemma entireCauchyCoefficient_deriv {f : ℂ → ℂ} (hf : Differentiable ℂ f) (n : ℕ) :
    entireCauchyCoefficient (deriv f) n = entireCauchyCoefficient f (n+1) * (n+1) := by
  have hd : Differentiable ℂ (deriv f) := differentiableOn_univ.mp (hf.differentiableOn.deriv isOpen_univ)
  have h1 := entireCauchyCoefficient_factorial hd n
  have h2 := entireCauchyCoefficient_factorial hf (n+1)
  rw [iteratedDeriv_succ'] at h2
  have hn : (n.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  apply mul_left_cancel₀ hn
  rw [h1, ← h2, Nat.factorial_succ, Nat.cast_mul]
  push_cast
  ring

lemma entireCauchyCoefficient_mul {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (n : ℕ) :
    entireCauchyCoefficient (fun z => f z*g z) n =
      ∑ ij ∈ Finset.antidiagonal n, entireCauchyCoefficient f ij.1 * entireCauchyCoefficient g ij.2 := by
  apply entireCauchyCoefficient_eq_of_hasSum (hf.mul hg)
  intro z
  have hfn : Summable (fun i => ‖entireCauchyCoefficient f i * z^i‖) := by
    simpa only [norm_mul, norm_pow] using entireCauchyCoefficient_norm_summable hf ‖z‖ (norm_nonneg z)
  have hgn : Summable (fun i => ‖entireCauchyCoefficient g i * z^i‖) := by
    simpa only [norm_mul, norm_pow] using entireCauchyCoefficient_norm_summable hg ‖z‖ (norm_nonneg z)
  have h := (summable_norm_sum_mul_antidiagonal_of_summable_norm hfn hgn).of_norm.hasSum
  rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hgn,
    (entireCauchyCoefficient_hasSum hf z).tsum_eq,
    (entireCauchyCoefficient_hasSum hg z).tsum_eq] at h
  convert h using 1
  funext m
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have he := Finset.mem_antidiagonal.mp hij
  rw [← he, pow_add]
  ring

lemma entireFormalTaylor_deriv {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    entireFormalTaylor (deriv f) = PowerSeries.derivative ℂ (entireFormalTaylor f) := by
  ext n
  simp [PowerSeries.coeff_derivative, entireCauchyCoefficient_deriv hf]

lemma entireFormalTaylor_mul {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) :
    entireFormalTaylor (fun z => f z*g z) = entireFormalTaylor f * entireFormalTaylor g := by
  ext n
  simp [PowerSeries.coeff_mul, entireCauchyCoefficient_mul hf hg]
lemma entireCauchyCoefficient_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    entireCauchyCoefficient f 0 = f 0 := by
  exact (hf.hasFPowerSeriesOnBall 0 (R := 1) (by norm_num)).coeff_zero (fun _ => 1)

lemma entireFormalTaylor_polynomial (P : Polynomial ℂ) :
    entireFormalTaylor (fun z => P.eval z) = (P : PowerSeries ℂ) := by
  classical
  ext n
  rw [coeff_entireFormalTaylor, Polynomial.coeff_coe]
  apply entireCauchyCoefficient_eq_of_hasSum P.differentiable P.coeff
  intro z
  have hs : HasSum (fun n => P.coeff n*z^n)
      (∑ n ∈ P.support, P.coeff n*z^n) := hasSum_sum_of_ne_finset_zero (fun n hn => by
        rw [Polynomial.not_mem_support_iff.mp hn, zero_mul])
  simpa only [Polynomial.eval_eq_sum, Polynomial.sum_def] using hs

/-- An actual analytic logarithmic-derivative equation implies the genuine
formal power-series equation used by arithmetic recovery. -/
theorem entireFormalTaylor_phase_equation {w : ℂ → ℂ} (hw : Differentiable ℂ w)
    (hnz : ∀ z, w z ≠ 0) (P : Polynomial ℂ)
    (hp : ∀ z, HasDerivAt (fun t => P.eval t) (deriv w z / w z) z) :
    PowerSeries.derivative ℂ (entireFormalTaylor w) =
      (P.derivative : PowerSeries ℂ) * entireFormalTaylor w := by
  have hfun : deriv w = fun z => P.derivative.eval z * w z := by
    funext z
    rw [(P.hasDerivAt z).unique (hp z), div_mul_cancel₀ _ (hnz z)]
  rw [← entireFormalTaylor_deriv hw, hfun,
    entireFormalTaylor_mul P.derivative.differentiable hw, entireFormalTaylor_polynomial]

end StrictEUnit
#print axioms StrictEUnit.entireFormalTaylor
#print axioms StrictEUnit.coeff_entireFormalTaylor
#print axioms StrictEUnit.entireCauchyCoefficient_eq_of_hasSum
#print axioms StrictEUnit.entireCauchyCoefficient_factorial
#print axioms StrictEUnit.entireCauchyCoefficient_deriv
#print axioms StrictEUnit.entireCauchyCoefficient_mul
#print axioms StrictEUnit.entireFormalTaylor_deriv
#print axioms StrictEUnit.entireFormalTaylor_mul

#print axioms StrictEUnit.entireCauchyCoefficient_zero
#print axioms StrictEUnit.entireFormalTaylor_polynomial
#print axioms StrictEUnit.entireFormalTaylor_phase_equation
