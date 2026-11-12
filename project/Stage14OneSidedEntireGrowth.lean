import EntireUnitExponentialPolynomial

/-! One-sided growth is sufficient for a genuine zero-free entire function.
This does not assume any bound on its reciprocal. The normalized entire
logarithm and the real-part-to-modulus estimate are actual analytic results. -/
noncomputable section
open Complex Metric Set
namespace StrictEUnit

/-- An upper bound alone on the real part outside the unit disk suffices.
Continuity fills the compact disk, and positive N absorbs the logarithm. -/
theorem entire_polynomial_of_exterior_real_part_upper_growth {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hf0 : f 0 = 0) (C M : ℝ)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (N : ℕ) (hN : 0 < N)
    (hre : ∀ z : ℂ, 1 ≤ ‖z‖ → (f z).re ≤ C*‖z‖^N + M*Real.log ‖z‖ + C) :
    ∃ P : Polynomial ℂ, (∀ z : ℂ, P.eval z = f z) ∧ P.natDegree ≤ N := by
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0:ℂ) 1).exists_bound_of_continuousOn
    hf.continuous.continuousOn
  let D : ℝ := |K| + 2*C + M
  have hD : 0 ≤ D := by dsimp [D]; positivity
  apply entire_polynomial_of_real_part_growth hf hf0 D hD N
  intro z
  have ht : 0 ≤ ‖z‖ := norm_nonneg z
  have hbase : 1 ≤ 1+‖z‖ := by linarith
  have hpow : 1 ≤ (1+‖z‖)^N := one_le_pow₀ hbase
  by_cases hz : 1 ≤ ‖z‖
  · have hp : ‖z‖^N ≤ (1+‖z‖)^N := pow_le_pow_left₀ ht (by linarith) N
    have hl : Real.log ‖z‖ ≤ (1+‖z‖)^N :=
      (Real.log_le_self (lt_of_lt_of_le zero_lt_one hz).le).trans
        ((by linarith : ‖z‖ ≤ 1+‖z‖).trans (le_self_pow₀ hbase hN.ne'))
    have hh := hre z hz
    have hcp := mul_le_mul_of_nonneg_left hp hC
    have hml := mul_le_mul_of_nonneg_left hl hM
    have hc1 := mul_le_mul_of_nonneg_left hpow hC
    have hk0 : 0 ≤ |K| *(1+‖z‖)^N := by positivity
    dsimp [D]
    nlinarith
  · have hh : (f z).re ≤ K := (Complex.re_le_norm _).trans
      (hK z (by simpa [mem_closedBall, dist_zero_right] using (le_of_not_ge hz)))
    have hk : K ≤ |K| := le_abs_self K
    have hkd : |K| ≤ D := by dsimp [D]; linarith
    exact hh.trans (hk.trans (hkd.trans (by nlinarith)))

/-- The actual normalized logarithm inherits an upper real-part bound from
w alone. No lower real-part bound or reciprocal growth is used. -/
theorem real_part_upper_bound_of_one_sided_unit_growth {w g : ℂ → ℂ} {N : ℕ}
    (hN : 0 < N) (hnz : ∀ z, w z ≠ 0)
    (hlog : ∀ z, w z = w 0 * Complex.exp (g z))
    (hw : HasPowerExponentialBound N w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, 1 ≤ ‖z‖ → (g z).re ≤ C*‖z‖^N + C := by
  obtain ⟨D, hD, hDw⟩ := log_norm_le_of_power_exponential_bound hN hnz hw
  let K := Real.log ‖w 0‖
  refine ⟨D + |K|, by positivity, ?_⟩
  intro z hz
  have he : Real.log ‖w z‖ = K + (g z).re := by
    rw [hlog z, norm_mul, Complex.norm_exp,
      Real.log_mul (norm_ne_zero_iff.mpr (hnz 0)) (Real.exp_ne_zero _), Real.log_exp]
  have hu := hDw z hz
  rw [he] at hu
  have hk : 0 ≤ |K| * ‖z‖^N := by positivity
  nlinarith [neg_abs_le K]

/-- A genuine zero-free entire function with only an upper growth bound is
its value at zero times an exponential polynomial of degree at most N. -/
theorem entire_unit_eq_exp_polynomial_of_one_sided_growth {w : ℂ → ℂ} {N : ℕ}
    (hN : 0 < N) (hw : Differentiable ℂ w) (hnz : ∀ z, w z ≠ 0)
    (hgrowth : HasPowerExponentialBound N w) :
    ∃ P : Polynomial ℂ, P.coeff 0 = 0 ∧ P.natDegree ≤ N ∧
      (∀ z, w z = w 0 * Complex.exp (P.eval z)) ∧
      ∀ z, HasDerivAt (fun t => P.eval t) (deriv w z / w z) z := by
  obtain ⟨g, hg0, hg, hgd, hlog⟩ := exists_normalized_entire_logarithm hw hnz
  obtain ⟨C, hC, hbound⟩ := real_part_upper_bound_of_one_sided_unit_growth
    hN hnz hlog hgrowth
  obtain ⟨P, hP, hdegree⟩ := entire_polynomial_of_exterior_real_part_upper_growth
    hg hg0 C 0 hC (le_refl 0) N hN (fun z hz => by simpa using hbound z hz)
  refine ⟨P, ?_, hdegree, ?_, ?_⟩
  · simpa [hg0, Polynomial.coeff_zero_eq_eval_zero] using hP 0
  · intro z
    rw [hP]
    exact hlog z
  · have he : (fun z => P.eval z) = g := funext hP
    rw [he]
    exact hgd

/-- Degree at most one and zero constant term identify the actual linear phase. -/
theorem eval_eq_coeff_one_mul_of_natDegree_le_one {P : Polynomial ℂ}
    (hP0 : P.coeff 0 = 0) (hP : P.natDegree ≤ 1) (z : ℂ) :
    P.eval z = P.coeff 1 * z := by
  conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one hP]
  simp [hP0]

/-- The exponential-type specialization needs no reciprocal estimate. -/
theorem entire_unit_eq_exp_linear_of_one_sided_growth {w : ℂ → ℂ}
    (hw : Differentiable ℂ w) (hnz : ∀ z, w z ≠ 0)
    (hgrowth : HasPowerExponentialBound 1 w) :
    ∃ a : ℂ, ∀ z, w z = w 0 * Complex.exp (a*z) := by
  obtain ⟨P, hP0, hPN, hP, _⟩ :=
    entire_unit_eq_exp_polynomial_of_one_sided_growth (by decide) hw hnz hgrowth
  exact ⟨P.coeff 1, fun z => by rw [hP z, eval_eq_coeff_one_mul_of_natDegree_le_one hP0 hPN]⟩

end StrictEUnit
#print axioms StrictEUnit.entire_polynomial_of_exterior_real_part_upper_growth
#print axioms StrictEUnit.real_part_upper_bound_of_one_sided_unit_growth
#print axioms StrictEUnit.entire_unit_eq_exp_polynomial_of_one_sided_growth
#print axioms StrictEUnit.eval_eq_coeff_one_mul_of_natDegree_le_one
#print axioms StrictEUnit.entire_unit_eq_exp_linear_of_one_sided_growth
