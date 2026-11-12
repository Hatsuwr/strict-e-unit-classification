import PolynomialNonresidueValuation

noncomputable section
namespace StrictEUnit

/-- Any integral algebraic exponent with a defining polynomial rootless
modulo every prime in one unit progression violates binomial arithmetic.
All p-places and weighted prime supply are constructed, not assumed. -/
theorem numberField_no_binomial_of_rootless_progression
    {K : Type*} [Field K] [NumberField K]
    (a : K) (ha : IsIntegral ℤ a) (P : Polynomial ℤ)
    (hroot : P.eval₂ (Int.castRingHom K) a = 0)
    {q : ℕ} [NeZero q] (b : ZMod q) (hb : IsUnit b)
    (hnr : ∀ p : ℕ, p.Prime → (p : ZMod q) = b →
      ∀ x : ZMod p, P.eval₂ (Int.castRingHom (ZMod p)) x ≠ 0) :
    ¬ BinomialPrefixDenominators a := by
  classical
  let v : ℕ → Valuation K (WithZero (Multiplicative ℤ)) := fun p =>
    if h : p.Prime then (numberField_exists_prime_place K p h).choose
    else (numberField_exists_prime_place K 2 Nat.prime_two).choose
  have hvp (p : ℕ) (hp : p.Prime) : v p (p : K) < 1 := by
    dsimp only [v]
    rw [dif_pos hp]
    exact (numberField_exists_prime_place K p hp).choose_spec
  apply no_binomialPrefixDenominators_of_progression_certificates a b hb v
  · exact fun p hp _ => hvp p hp
  · intro p hp h r _
    exact polynomial_nonresidue_translate_unit (v p) p hp (hvp p hp)
      a ha P hroot (hnr p hp h) r

end StrictEUnit
end
