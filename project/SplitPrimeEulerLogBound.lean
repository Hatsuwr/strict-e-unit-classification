import SplitPrimeNormCertificates
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
open scoped NumberField nonZeroDivisors BigOperators
open NumberField Finset
namespace StrictEUnit

theorem log_one_add_quadratic_lower {x : ℝ} (hx : 0 ≤ x) :
    x - x^2/2 ≤ Real.log (1+x) := by
  apply le_trans _ (Real.le_log_one_add_of_nonneg hx)
  apply (le_div_iff₀ (by linarith : 0 < x+2)).mpr
  have h := mul_nonneg (sq_nonneg x) hx
  nlinarith

theorem galois_split_prime_product_lower
    (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    {s : ℝ} (hs : 1 < s) (S : Finset ℕ)
    (hp : ∀ p ∈ S, p.Prime)
    (he : ∀ p ∈ S, Ideal.ramificationIdxIn (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 K) = 1)
    (hf : ∀ p ∈ S, Ideal.inertiaDegIn (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 K) = 1) :
    ∏ p ∈ S, (1 + (Module.finrank ℚ K : ℝ) / (p : ℝ)^s) ≤
      ‖idealNormLSeries K (s : ℂ)‖ := by
  apply idealNormLSeries_certified_prime_product_lower K hs S _ hp
  intro p hmem
  exact galois_split_prime_norm_certificate K p (hp p hmem) (he p hmem) (hf p hmem)

/-- Logarithmic lower estimate with explicit quadratic error on a finite set
of primes satisfying the actual Galois e=f=1 criterion. -/
theorem galois_split_prime_log_lower
    (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    {s : ℝ} (hs : 1 < s) (S : Finset ℕ)
    (hp : ∀ p ∈ S, p.Prime)
    (he : ∀ p ∈ S, Ideal.ramificationIdxIn (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 K) = 1)
    (hf : ∀ p ∈ S, Ideal.inertiaDegIn (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 K) = 1) :
    ∑ p ∈ S, ((Module.finrank ℚ K : ℝ) / (p : ℝ)^s -
      ((Module.finrank ℚ K : ℝ) / (p : ℝ)^s)^2/2) ≤
      Real.log ‖idealNormLSeries K (s : ℂ)‖ := by
  have hpos (p : ℕ) : 0 < 1 + (Module.finrank ℚ K : ℝ) / (p : ℝ)^s := by positivity
  calc
    _ ≤ ∑ p ∈ S, Real.log (1 + (Module.finrank ℚ K : ℝ) / (p : ℝ)^s) := by
      apply sum_le_sum
      intro p _
      apply log_one_add_quadratic_lower
      positivity
    _ = Real.log (∏ p ∈ S, (1 + (Module.finrank ℚ K : ℝ) / (p : ℝ)^s)) := by
      rw [Real.log_prod S _ (fun p _ => (hpos p).ne')]
    _ ≤ _ := Real.log_le_log (prod_pos (fun p _ => hpos p))
      (galois_split_prime_product_lower K hs S hp he hf)

/-- A uniform analytic constraint on all finite genuinely split prime sets,
with its constant derived from ideal geometry rather than prime supply. -/
theorem galois_split_prime_log_upper_constraint
    (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K] :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℝ), 1 < s → ∀ (S : Finset ℕ),
      (∀ p ∈ S, p.Prime) →
      (∀ p ∈ S, Ideal.ramificationIdxIn (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 K) = 1) →
      (∀ p ∈ S, Ideal.inertiaDegIn (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 K) = 1) →
      (∑ p ∈ S, ((Module.finrank ℚ K : ℝ) / (p : ℝ)^s -
        ((Module.finrank ℚ K : ℝ) / (p : ℝ)^s)^2/2)) ≤
        Real.log (s * C / (s - 1)) := by
  obtain ⟨C, hC0, hC⟩ := idealNormLSeries_simple_pole_bound K
  refine ⟨C+1, by linarith, ?_⟩
  intro s hs S hp he hf
  apply (galois_split_prime_log_lower K hs S hp he hf).trans
  have hn : 1 ≤ ‖idealNormLSeries K (s : ℂ)‖ := by
    simpa using idealNormLSeries_prime_linear_product_lower K hs ∅
  apply Real.log_le_log (by linarith)
  apply (hC s hs).trans
  apply div_le_div_of_nonneg_right
  · apply mul_le_mul_of_nonneg_left (by linarith)
    linarith
  · linarith

end StrictEUnit
end
