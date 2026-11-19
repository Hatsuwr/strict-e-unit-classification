import CertifiedPrimeSummability
import Mathlib.NumberTheory.LSeries.PrimesInAP

noncomputable section
attribute [local instance] Classical.propDecidable
namespace StrictEUnit

/-- The actual Mathlib Dirichlet-series theorem, converted to the exact
prime-weight convention used by the binomial denominator obstruction. -/
theorem arithmetic_progression_prime_weight_not_summable
    {q : ℕ} [NeZero q] (b : ZMod q) (hb : IsUnit b) :
    ¬ Summable (fun p : ℕ =>
      if p.Prime ∧ (p : ZMod q) = b then Real.log (p : ℝ)/(p : ℝ) else 0) := by
  have h := ArithmeticFunction.vonMangoldt.not_summable_residueClass_prime_div hb
  convert h using 1
  apply summable_congr
  intro p
  by_cases hp : p.Prime
  · by_cases hr : (p : ZMod q) = b
    · simp [hp, hr, ArithmeticFunction.vonMangoldt.residueClass,
        ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simp [hp, hr, ArithmeticFunction.vonMangoldt.residueClass]
  · simp [hp]

/-- A genuine arithmetic-progression special case: local certificates on
all primes in one unit progression contradict binomial prefix arithmetic.
This does not assert that arbitrary irrational exponents have these places. -/
theorem no_binomialPrefixDenominators_of_progression_certificates
    {K Γ₀ : Type*} [Field K] [CharZero K] [LinearOrderedCommGroupWithZero Γ₀]
    (a : K) {q : ℕ} [NeZero q] (b : ZMod q) (hb : IsUnit b)
    (v : ℕ → Valuation K Γ₀)
    (hvp : ∀ p : ℕ, p.Prime → (p : ZMod q) = b → v p (p : K) < 1)
    (hu : ∀ p : ℕ, p.Prime → (p : ZMod q) = b →
      ∀ r : ℕ, r < p → v p (a - (r : K)) = 1) :
    ¬ BinomialPrefixDenominators a := by
  apply no_binomialPrefixDenominators_of_certified_prime_divergence a
    {p | p.Prime ∧ (p : ZMod q) = b} v
  · exact fun p h => h.1
  · exact fun p h => hvp p h.1 h.2
  · exact fun p h => hu p h.1 h.2
  · intro hs
    apply arithmetic_progression_prime_weight_not_summable b hb
    apply (summable_congr (fun p => ?_)).mp hs
    by_cases h : p.Prime ∧ (p : ZMod q) = b
    · simp [h]
    · simp [h]

end StrictEUnit
end
