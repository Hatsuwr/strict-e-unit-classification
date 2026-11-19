import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open scoped Topology
open Filter Set
namespace StrictEUnit

/-- A genuine pole with nonzero leading limit cannot have a finite right limit. -/
theorem v5_right_limit_excludes_pole {f : ℝ → ℂ} {c d : ℂ} {N : ℕ}
    (hN : 0 < N) (hf : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 d))
    (hlead : Tendsto (fun x : ℝ => (x : ℂ)^N * f x) (𝓝[>] 0) (𝓝 c)) : c = 0 := by
  have hx : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hh := (hx.pow N).mul hf
  simp only [zero_pow (Nat.ne_of_gt hN), zero_mul] at hh
  exact tendsto_nhds_unique hlead hh

/-- For a finite Laurent expression P(x)/x^N with nonzero constant numerator,
a finite limit at zero rules out every negative leading exponent. -/
theorem v5_polynomial_over_power_finite_limit {P : Polynomial ℂ} {N : ℕ} {d : ℂ}
    (hP : P.eval 0 ≠ 0)
    (hf : Tendsto (fun x : ℝ => P.eval (x : ℂ) / (x : ℂ)^N)
      (𝓝[>] 0) (𝓝 d)) : N = 0 := by
  by_contra hN
  apply hP
  apply v5_right_limit_excludes_pole (Nat.pos_of_ne_zero hN) hf
  have he : (fun x : ℝ => (x : ℂ)^N * (P.eval (x : ℂ) / (x : ℂ)^N))
      =ᶠ[𝓝[>] 0] (fun x : ℝ => P.eval (x : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx : x ≠ 0)
    exact mul_div_cancel₀ _ (pow_ne_zero N hx0)
  exact ((P.continuous.comp Complex.continuous_ofReal).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds).congr' he.symm

/-- The normalized logarithmic-derivative equation forces the Laurent coefficient
function to tend to the integer residue. Derivative continuity/limits remain explicit. -/
theorem v5_normalized_rank_one_coefficient_limit
    (W D b : ℝ → ℂ) (q c d : ℂ) (hc : c ≠ 0)
    (hW : Tendsto W (𝓝[>] (0 : ℝ)) (𝓝 c))
    (hD : Tendsto D (𝓝[>] (0 : ℝ)) (𝓝 d))
    (heq : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), (x : ℂ) * D x = (b x - q) * W x) :
    Tendsto b (𝓝[>] (0 : ℝ)) (𝓝 q) := by
  have hx : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hn : ∀ᶠ x in 𝓝[>] (0 : ℝ), W x ≠ 0 := hW.eventually (isOpen_ne.mem_nhds hc)
  have hb : b =ᶠ[𝓝[>] (0 : ℝ)] (fun x => q + ((x : ℂ) * D x) / W x) := by
    filter_upwards [heq, hn] with x he hn
    rw [he, mul_div_cancel_right₀ _ hn]
    ring
  have hh := (tendsto_const_nhds (x := q)).add ((hx.mul hD).div hW hc)
  simp only [zero_mul, zero_div, add_zero] at hh
  exact hh.congr' hb.symm

/-- The normalized ODE rules out a reduced negative Laurent leading exponent.
The reduced numerator and the analytic limits are explicit inputs. -/
theorem v5_rank_one_reduced_pole_exclusion
    (W D b : ℝ → ℂ) (q c d : ℂ) (hc : c ≠ 0)
    (hW : Tendsto W (𝓝[>] (0 : ℝ)) (𝓝 c))
    (hD : Tendsto D (𝓝[>] (0 : ℝ)) (𝓝 d))
    (heq : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), (x : ℂ) * D x = (b x - q) * W x)
    (P : Polynomial ℂ) (N : ℕ) (hP : P.eval 0 ≠ 0)
    (hrep : b =ᶠ[𝓝[>] (0 : ℝ)] (fun x : ℝ => P.eval (x : ℂ) / (x : ℂ)^N)) :
    N = 0 ∧ P.eval 0 = q := by
  have hb := v5_normalized_rank_one_coefficient_limit W D b q c d hc hW hD heq
  have hquot := hb.congr' hrep
  have hN := v5_polynomial_over_power_finite_limit hP hquot
  refine ⟨hN, ?_⟩
  simp only [hN, pow_zero, div_one] at hquot
  exact tendsto_nhds_unique
    ((P.continuous.comp Complex.continuous_ofReal).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds) hquot

end StrictEUnit
#print axioms StrictEUnit.v5_right_limit_excludes_pole
#print axioms StrictEUnit.v5_polynomial_over_power_finite_limit
#print axioms StrictEUnit.v5_normalized_rank_one_coefficient_limit

#print axioms StrictEUnit.v5_rank_one_reduced_pole_exclusion
