import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
This file formalizes the limiting argument AFTER the Fourier coefficient bound
in equation (25) of the proposed strict E-unit manuscript. It does not assume or
prove that the Fourier bound follows from the analytic construction in the paper.
All bounds below are hypotheses, not axioms of the development.
-/

open Filter Topology

namespace StrictEUnit

/-- The complete right side of manuscript equation (25) tends to zero for j > N.
No sign assumptions on C and M are needed for this limit. -/
theorem fourier_bound_tends_zero (C M : ℝ) {N j : ℕ} (hNj : N < j) :
    Tendsto (fun r : ℝ => 2 * (C * r ^ N + M * Real.log r + C) / r ^ j)
      atTop (𝓝 0) := by
  have hj : 0 < j := lt_of_le_of_lt (Nat.zero_le N) hNj
  have hp : Tendsto (fun r : ℝ => r ^ N / r ^ j) atTop (𝓝 0) :=
    tendsto_pow_div_pow_atTop_zero hNj
  have hl : Tendsto (fun r : ℝ => Real.log r / r ^ j) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_atTop (show (0 : ℝ) < (j : ℝ) by exact_mod_cast hj)).tendsto_div_nhds_zero
  have hc : Tendsto (fun r : ℝ => 1 / r ^ j) atTop (𝓝 0) := by
    simpa only [pow_zero] using
      (tendsto_pow_div_pow_atTop_zero (𝕜 := ℝ) hj)
  have hsum := (((hp.const_mul C).add (hl.const_mul M)).add (hc.const_mul C)).const_mul 2
  convert hsum using 1
  · funext r
    ring
  · simp

/-- An arbitrarily-large-radius estimate proves exact vanishing, not just a
small numerical upper bound. This is the j > N step of equation (25). -/
theorem coefficient_eq_zero_of_fourier_bound (a : ℂ) (C M : ℝ) {N j : ℕ}
    (hNj : N < j)
    (hbound : ∀ r : ℝ, 1 ≤ r →
      ‖a‖ ≤ 2 * (C * r ^ N + M * Real.log r + C) / r ^ j) : a = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg a)
  apply ge_of_tendsto (fourier_bound_tends_zero C M hNj)
  exact (eventually_ge_atTop (1 : ℝ)).mono fun r hr => hbound r hr

/-- The conclusion applies simultaneously to every index beyond N. -/
theorem coefficients_above_cutoff_vanish (a : ℕ → ℂ) (C M : ℝ) (N : ℕ)
    (hbound : ∀ j : ℕ, N < j → ∀ r : ℝ, 1 ≤ r →
      ‖a j‖ ≤ 2 * (C * r ^ N + M * Real.log r + C) / r ^ j) :
    ∀ j : ℕ, N < j → a j = 0 := by
  intro j hj
  exact coefficient_eq_zero_of_fourier_bound (a j) C M hj (hbound j hj)

/-- Exact coefficient-level polynomial reconstruction, rather than a finite
numerical truncation. To identify an analytic function with this polynomial,
one still needs its Taylor expansion/uniqueness theorem. -/
theorem exists_polynomial_of_fourier_bound (a : ℕ → ℂ) (C M : ℝ) (N : ℕ)
    (hbound : ∀ j : ℕ, N < j → ∀ r : ℝ, 1 ≤ r →
      ‖a j‖ ≤ 2 * (C * r ^ N + M * Real.log r + C) / r ^ j) :
    ∃ P : Polynomial ℂ, ∀ j, P.coeff j = a j := by
  classical
  refine ⟨∑ n ∈ Finset.range (N + 1), Polynomial.monomial n (a n), ?_⟩
  intro j
  by_cases hj : j < N + 1
  · simp [Polynomial.coeff_sum, Polynomial.coeff_monomial, hj]
  · have hz : a j = 0 := coefficients_above_cutoff_vanish a C M N hbound j (by omega)
    simp [Polynomial.coeff_sum, Polynomial.coeff_monomial, hj, hz]

end StrictEUnit

#print axioms StrictEUnit.fourier_bound_tends_zero
#print axioms StrictEUnit.coefficient_eq_zero_of_fourier_bound
#print axioms StrictEUnit.coefficients_above_cutoff_vanish
#print axioms StrictEUnit.exists_polynomial_of_fourier_bound
