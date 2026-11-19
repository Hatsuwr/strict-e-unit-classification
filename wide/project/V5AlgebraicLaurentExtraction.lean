import V5LaurentExtraction
import V5PolynomialRecovery

noncomputable section
namespace StrictEUnit

/-- The meromorphic growth bounds and algebraic pointwise equations recover
an actual Laurent polynomial over the algebraically closed coefficient field. -/
theorem v5_algebraic_laurent_of_weighted_growth {k : Type*}
    [Field k] [CharZero k] [IsAlgClosed k] (ι : k →+* ℂ)
    {f : ℂ → ℂ} (m N : ℕ)
    (hf : ∀ z ≠ 0, DifferentiableAt ℂ f z)
    (C D : ℝ) (hD : 0 ≤ D)
    (hb : ∀ z ≠ 0, ‖z‖ < 1 → ‖z ^ m * f z‖ ≤ C)
    (hg : ∀ z, 1 ≤ ‖z‖ → ‖z ^ m * f z‖ ≤ D * ‖z‖ ^ N)
    (hmonic : ∀ a : k, a ≠ 0 →
      ∃ p : Polynomial k, p.Monic ∧ p.eval₂ ι (f (ι a)) = 0) :
    ∃ L : LaurentPolynomial k, ∀ z : ℂˣ, LaurentPolynomial.eval₂ ι z L = f z := by
  obtain ⟨P, _, hP⟩ := v5_laurent_numerator_of_weighted_growth m N hf C D hD hb hg
  obtain ⟨Q, hQ⟩ := v5_polynomial_of_monic_laurent_samples ι P m f (by
    intro a ha
    have hn : ι a ≠ 0 := (map_ne_zero_iff ι ι.injective).mpr ha
    rw [mul_comm]
    exact ((eq_div_iff (pow_ne_zero m hn)).mp (hP (ι a) hn)).symm) hmonic
  refine ⟨Polynomial.toLaurent Q * LaurentPolynomial.T (-(m : ℤ)), fun z => ?_⟩
  rw [map_mul, LaurentPolynomial.eval₂_toLaurent, LaurentPolynomial.eval₂_T_neg_n]
  rw [← Polynomial.eval_map, hQ, hP z (Units.ne_zero z)]
  simp only [div_eq_mul_inv, inv_pow, Units.val_inv_eq_inv_val]

end StrictEUnit
#print axioms StrictEUnit.v5_algebraic_laurent_of_weighted_growth
