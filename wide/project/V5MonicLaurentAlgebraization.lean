import V5MonicLaurentGrowth
import V5AlgebraicLaurentExtraction
import V5LaurentMonicSpecialization

noncomputable section
namespace StrictEUnit

/-- Growth is derived from the fixed monic equation; only the independent arithmetic
sample premise of the checked recovery theorem remains explicit. -/
theorem v5_algebraic_laurent_of_monic_equation_and_samples {k : Type*}
    [Field k] [CharZero k] [IsAlgClosed k] (ι : k →+* ℂ)
    {p : Polynomial (LaurentPolynomial k)} (hp : p.Monic)
    (q : ℕ) (f : ℂ → ℂ) (hf : ∀ z ≠ 0, DifferentiableAt ℂ f z)
    (heq : ∀ t : ℂˣ, (p.map (LaurentPolynomial.eval₂ ι (t^q))).IsRoot (f t))
    (hmonic : ∀ a : k, a ≠ 0 →
      ∃ p : Polynomial k, p.Monic ∧ p.eval₂ ι (f (ι a)) = 0) :
    ∃ L : LaurentPolynomial k, ∀ z : ℂˣ, LaurentPolynomial.eval₂ ι z L = f z := by
  obtain ⟨C, hC, m, hb, hg⟩ := v5_monic_laurent_function_weighted_growth ι hp q f heq
  exact v5_algebraic_laurent_of_weighted_growth ι m (m+m) hf C C hC hb hg hmonic

/-- A global monic Laurent relation after a power substitution suffices for
algebraization over the original algebraically closed coefficient field. -/
theorem v5_algebraic_laurent_of_monic_laurent_equation {k : Type*}
    [Field k] [CharZero k] [IsAlgClosed k] (ι : k →+* ℂ)
    {p : Polynomial (LaurentPolynomial k)} (hp : p.Monic)
    (q : ℕ) (f : ℂ → ℂ) (hf : ∀ z ≠ 0, DifferentiableAt ℂ f z)
    (heq : ∀ t : ℂˣ, (p.map (LaurentPolynomial.eval₂ ι (t^q))).IsRoot (f t)) :
    ∃ L : LaurentPolynomial k, ∀ z : ℂˣ, LaurentPolynomial.eval₂ ι z L = f z := by
  apply v5_algebraic_laurent_of_monic_equation_and_samples ι hp q f hf heq
  intro a ha
  let t := Units.mk0 a ha
  refine ⟨v5LaurentSpecialize (RingHom.id k) t q p,
    v5LaurentSpecialize_monic _ _ _ _ hp, ?_⟩
  rw [← Polynomial.eval_map, v5LaurentSpecialize_map]
  exact heq (Units.map ι.toMonoidHom t)

end StrictEUnit
#print axioms StrictEUnit.v5_algebraic_laurent_of_monic_equation_and_samples

#print axioms StrictEUnit.v5_algebraic_laurent_of_monic_laurent_equation
