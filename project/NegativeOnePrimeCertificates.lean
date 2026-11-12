import QuadraticNonresidueValuation
import Mathlib.NumberTheory.LegendreSymbol.Basic

noncomputable section
namespace StrictEUnit
variable {K Γ₀ : Type*} [Field K] [CharZero K] [LinearOrderedCommGroupWithZero Γ₀]

/-- For an actual square root of minus one, every p-place at p=3 mod 4
has all the requisite translate-unit certificates. -/
theorem negative_one_translate_unit (a : K) (ha : a^2 = -1)
    (p : ℕ) (hp : p.Prime) (hmod : p % 4 = 3)
    (v : Valuation K Γ₀) (hvp : v (p : K) < 1) :
    ∀ j : ℕ, v (a - (j : K)) = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  apply quadratic_nonresidue_translate_unit v p hp hvp a (-1)
  · simpa using ha
  · intro x hx
    have hx' : x^2 = -1 := by simpa using hx
    exact ZMod.mod_four_ne_three_of_sq_eq_neg_one hx' hmod

/-- Dirichlet divergence and the actual quadratic equation discharge the
prime supply and residue tests. The existence of the p-places is still explicit. -/
theorem no_binomialPrefixDenominators_square_neg_one_of_places
    (a : K) (ha : a^2 = -1) (v : ℕ → Valuation K Γ₀)
    (hvp : ∀ p : ℕ, p.Prime → p % 4 = 3 → v p (p : K) < 1) :
    ¬ BinomialPrefixDenominators a := by
  have hu : IsUnit (3 : ZMod 4) := ⟨⟨3, 3, by decide, by decide⟩, rfl⟩
  have hmod (p : ℕ) (h : (p : ZMod 4) = 3) : p % 4 = 3 := by
    have hh := congrArg ZMod.val h
    simpa using hh
  apply no_binomialPrefixDenominators_of_progression_certificates a (3 : ZMod 4) hu v
  · exact fun p hp h => hvp p hp (hmod p h)
  · intro p hp h r _
    exact negative_one_translate_unit a ha p hp (hmod p h) (v p)
      (hvp p hp (hmod p h)) r

end StrictEUnit
end
