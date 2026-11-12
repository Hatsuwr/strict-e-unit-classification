import ElementaryGeneratorGrowth
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! The actual exponential generating series of geometrically bounded
coefficients converges everywhere and has an explicit exponential-type
bound. This does not define strict E-functions or prove arithmetic/ODE
properties of their coefficients. -/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- The actual factorial-normalized generating series. -/
def exponentialGeneratingFunction (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, a n * z^n / (n.factorial : ℂ)

/-- The real exponential series is an explicit summable majorant. -/
theorem geometric_egf_majorant_hasSum (C : ℝ) (z : ℂ) :
    HasSum (fun n : ℕ => C * ((C * ‖z‖)^n / (n.factorial : ℝ)))
      (C * Real.exp (C * ‖z‖)) := by
  have h := NormedSpace.expSeries_div_hasSum_exp ℝ (C * ‖z‖)
  rw [← Real.exp_eq_exp_ℝ] at h
  exact h.mul_left C

/-- The coefficientwise majorization is proved with the actual factorials. -/
theorem geometric_egf_term_norm_le (a : ℕ → ℂ) (C : ℝ)
    (ha : ∀ n, ‖a n‖ ≤ C^(n+1)) (z : ℂ) (n : ℕ) :
    ‖a n * z^n / (n.factorial : ℂ)‖ ≤
      C * ((C * ‖z‖)^n / (n.factorial : ℝ)) := by
  calc
    _ = ‖a n‖ * ‖z‖^n / (n.factorial : ℝ) := by
      rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast]
    _ ≤ C^(n+1) * ‖z‖^n / (n.factorial : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (ha n) (pow_nonneg (norm_nonneg _) _)) (by positivity)
    _ = _ := by rw [pow_succ, mul_pow]; ring

/-- Everywhere convergence of the actual exponential generating series. -/
theorem geometric_egf_summable (a : ℕ → ℂ) (C : ℝ)
    (ha : ∀ n, ‖a n‖ ≤ C^(n+1)) (z : ℂ) :
    Summable (fun n : ℕ => a n * z^n / (n.factorial : ℂ)) :=
  Summable.of_norm_bounded _ (geometric_egf_majorant_hasSum C z).summable
    (geometric_egf_term_norm_le a C ha z)

/-- The actual series has its defined sum at every complex point. -/
theorem geometric_egf_hasSum (a : ℕ → ℂ) (C : ℝ)
    (ha : ∀ n, ‖a n‖ ≤ C^(n+1)) (z : ℂ) :
    HasSum (fun n : ℕ => a n * z^n / (n.factorial : ℂ))
      (exponentialGeneratingFunction a z) :=
  (geometric_egf_summable a C ha z).hasSum

/-- The desired exact exponential-type estimate follows from the series,
not from an assumed analytic growth estimate. -/
theorem geometric_egf_norm_le (a : ℕ → ℂ) (C : ℝ)
    (ha : ∀ n, ‖a n‖ ≤ C^(n+1)) (z : ℂ) :
    ‖exponentialGeneratingFunction a z‖ ≤ C * Real.exp (C * ‖z‖) :=
  (geometric_egf_hasSum a C ha z).norm_le_of_bounded
    (geometric_egf_majorant_hasSum C z) (geometric_egf_term_norm_le a C ha z)

/-- HasSum uniqueness transfers the derived estimate to an actual function
identified by its factorial-normalized series. -/
theorem function_norm_le_of_geometric_egf (a : ℕ → ℂ) (C : ℝ)
    (ha : ∀ n, ‖a n‖ ≤ C^(n+1)) (F : ℂ → ℂ)
    (hF : ∀ z, HasSum (fun n : ℕ => a n * z^n / (n.factorial : ℂ)) (F z)) (z : ℂ) :
    ‖F z‖ ≤ C * Real.exp (C * ‖z‖) := by
  rw [← (hF z).tsum_eq]
  exact geometric_egf_norm_le a C ha z

/-- The actual power pullback of this generating series satisfies the
manuscript's order-N bound, directly from geometric coefficient control. -/
theorem powerExponentialBound_geometric_egf_pullback {Ω : Type*}
    (N : ℕ) (z : Ω → ℂ) (a : ℕ → ℂ) (C : ℝ) (hC : 1 ≤ C)
    (ha : ∀ n, ‖a n‖ ≤ C^(n+1)) :
    HasPowerExponentialBoundOn N z
      (fun t => exponentialGeneratingFunction a (z t ^ N)) :=
  powerExponentialBound_power_pullback N z (exponentialGeneratingFunction a) C
    (lt_of_lt_of_le zero_lt_one hC) (geometric_egf_norm_le a C ha)

/-- The same bound for an actual series-identified function, rather than
only the named tsum construction. -/
theorem powerExponentialBound_function_of_geometric_egf {Ω : Type*}
    (N : ℕ) (z : Ω → ℂ) (a : ℕ → ℂ) (C : ℝ) (hC : 1 ≤ C)
    (ha : ∀ n, ‖a n‖ ≤ C^(n+1)) (F : ℂ → ℂ)
    (hF : ∀ w, HasSum (fun n : ℕ => a n * w^n / (n.factorial : ℂ)) (F w)) :
    HasPowerExponentialBoundOn N z (fun t => F (z t ^ N)) :=
  powerExponentialBound_power_pullback N z F C
    (lt_of_lt_of_le zero_lt_one hC) (function_norm_le_of_geometric_egf a C ha F hF)

end StrictEUnit
#print axioms StrictEUnit.exponentialGeneratingFunction
#print axioms StrictEUnit.geometric_egf_majorant_hasSum
#print axioms StrictEUnit.geometric_egf_term_norm_le
#print axioms StrictEUnit.geometric_egf_summable
#print axioms StrictEUnit.geometric_egf_hasSum
#print axioms StrictEUnit.geometric_egf_norm_le
#print axioms StrictEUnit.function_norm_le_of_geometric_egf
#print axioms StrictEUnit.powerExponentialBound_geometric_egf_pullback
#print axioms StrictEUnit.powerExponentialBound_function_of_geometric_egf
