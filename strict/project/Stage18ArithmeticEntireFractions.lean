import Stage14OneSidedArithmeticRecovery

/-! Arithmetic classification of actual fractions of entire functions.
Both factors carry their own genuine Taylor arithmetic and growth hypotheses.
The quotient is asserted only away from the origin; no formal realization or
meromorphic Taylor-arithmetic hypothesis is substituted for these conditions. -/
noncomputable section
namespace StrictEUnit

/-- Classify an actual fraction by classifying its numerator and denominator
separately. Positive growth degree is essential to the analytic input. -/
theorem stage18_entire_fraction_eq_zpow_subfield_exp_polynomial
    (k : Subfield ℂ) {f g : ℂ → ℂ} {N : ℕ}
    (hN : 0 < N) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hfnz : ∀ z, z ≠ 0 → f z ≠ 0) (hgnz : ∀ z, z ≠ 0 → g z ≠ 0)
    (hfgrowth : HasPowerExponentialBound N f)
    (hggrowth : HasPowerExponentialBound N g)
    (hfcoeff : ∀ n, entireCauchyCoefficient f n ∈ k)
    (hgcoeff : ∀ n, entireCauchyCoefficient g n ∈ k) :
    ∃ q : ℤ, ∃ c : k, ∃ P : Polynomial k,
      c ≠ 0 ∧ P.coeff 0 = 0 ∧ P.natDegree ≤ N ∧
      ∀ z : ℂ, z ≠ 0 →
        f z / g z = (c : ℂ) * z^q * Complex.exp ((P.map k.subtype).eval z) := by
  obtain ⟨m, a, A, _, ha, _, hA0, hAN, hA⟩ :=
    entire_eq_pow_subfield_exp_polynomial_of_one_sided_growth
      k hN hf hfnz hfgrowth hfcoeff
  obtain ⟨n, b, B, _, hb, _, hB0, hBN, hB⟩ :=
    entire_eq_pow_subfield_exp_polynomial_of_one_sided_growth
      k hN hg hgnz hggrowth hgcoeff
  refine ⟨(m : ℤ) - n, a / b, A - B, div_ne_zero ha hb, ?_, ?_, ?_⟩
  · simp only [Polynomial.coeff_sub, hA0, hB0, sub_self]
  · exact (Polynomial.natDegree_sub_le A B).trans (max_le hAN hBN)
  · intro z hz
    rw [hA z, hB z, Polynomial.map_sub, Polynomial.eval_sub, Complex.exp_sub,
      zpow_sub₀ hz, zpow_natCast, zpow_natCast]
    change ((a : ℂ) * z^m * Complex.exp ((A.map k.subtype).eval z)) /
      ((b : ℂ) * z^n * Complex.exp ((B.map k.subtype).eval z)) =
      ((a : ℂ) / (b : ℂ)) * (z^m / z^n) *
        (Complex.exp ((A.map k.subtype).eval z) / Complex.exp ((B.map k.subtype).eval z))
    simp only [mul_div_mul_comm]

/-- The integer monomial disappears at the genuine ordinary point one.
The exponential parameter is the polynomial's evaluation in the same field. -/
theorem stage18_entire_fraction_at_one_eq_subfield_scalar_exp
    (k : Subfield ℂ) {f g : ℂ → ℂ} {N : ℕ}
    (hN : 0 < N) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hfnz : ∀ z, z ≠ 0 → f z ≠ 0) (hgnz : ∀ z, z ≠ 0 → g z ≠ 0)
    (hfgrowth : HasPowerExponentialBound N f)
    (hggrowth : HasPowerExponentialBound N g)
    (hfcoeff : ∀ n, entireCauchyCoefficient f n ∈ k)
    (hgcoeff : ∀ n, entireCauchyCoefficient g n ∈ k) :
    ∃ c a : k, c ≠ 0 ∧ f 1 / g 1 = (c : ℂ) * Complex.exp (a : ℂ) := by
  obtain ⟨q, c, P, hc, _, _, hP⟩ :=
    stage18_entire_fraction_eq_zpow_subfield_exp_polynomial
      k hN hf hg hfnz hgnz hfgrowth hggrowth hfcoeff hgcoeff
  refine ⟨c, P.eval 1, hc, ?_⟩
  have he : (P.map k.subtype).eval 1 = (P.eval 1 : k) := by
    rw [Polynomial.eval_map]
    exact (Polynomial.eval₂_at_one k.subtype)
  simpa only [one_zpow, mul_one, he] using hP 1 one_ne_zero

end StrictEUnit
