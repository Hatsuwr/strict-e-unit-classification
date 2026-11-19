import OriginRemovalGrowth
import Stage14OneSidedEntireGrowth
import Mathlib.Topology.Algebra.Polynomial

/-! Analytic determinant-shaped classification from actual meromorphy,
nonvanishing off zero, and upper growth only. No determinant construction,
arithmetic coefficients, or differential system is supplied by these theorems. -/
noncomputable section
namespace StrictEUnit

/-- Removing the actual meromorphic order preserves the one-sided bound. -/
theorem exists_entire_remove_origin_with_one_sided_growth {v : ℂ → ℂ} {N : ℕ}
    (hm : MeromorphicAt v 0)
    (hd : ∀ z, z ≠ 0 → DifferentiableAt ℂ v z)
    (hnz : ∀ z, z ≠ 0 → v z ≠ 0)
    (hv : HasPowerExponentialBound N v) :
    ∃ q : ℤ, ∃ w : ℂ → ℂ,
      hm.order = (q : WithTop ℤ) ∧ Differentiable ℂ w ∧
      (∀ z, w z ≠ 0) ∧ (∀ z, z ≠ 0 → v z = z^q * w z) ∧
      HasPowerExponentialBound N w := by
  obtain ⟨q, w, hq, hwd, hwnz, hw, hvw⟩ := exists_entire_nonzero_remove_origin hm hd hnz
  refine ⟨q, w, hq, hwd, hwnz, hvw, ?_⟩
  apply powerExponentialBound_congr_exterior (powerExponentialBound_zpow_mul (-q) hv)
  intro z hz
  have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hz)
  exact (hw z hz0).symm

/-- Actual punctured analytic classification with only a bound on v itself.
The exponent q is the actual meromorphic order, not an assumed factorization. -/
theorem meromorphic_unit_eq_zpow_exp_polynomial_of_one_sided_growth
    {v : ℂ → ℂ} {N : ℕ} (hN : 0 < N) (hm : MeromorphicAt v 0)
    (hd : ∀ z, z ≠ 0 → DifferentiableAt ℂ v z)
    (hnz : ∀ z, z ≠ 0 → v z ≠ 0)
    (hv : HasPowerExponentialBound N v) :
    ∃ q : ℤ, ∃ c : ℂ, ∃ P : Polynomial ℂ,
      hm.order = (q : WithTop ℤ) ∧ c ≠ 0 ∧ P.coeff 0 = 0 ∧ P.natDegree ≤ N ∧
      ∀ z, z ≠ 0 → v z = c * z^q * Complex.exp (P.eval z) := by
  obtain ⟨q, w, hq, hwd, hwnz, hvw, hw⟩ :=
    exists_entire_remove_origin_with_one_sided_growth hm hd hnz hv
  obtain ⟨P, hP0, hPN, hP, _⟩ :=
    entire_unit_eq_exp_polynomial_of_one_sided_growth hN hwd hwnz hw
  refine ⟨q, w 0, P, hq, hwnz 0, hP0, hPN, fun z hz => ?_⟩
  rw [hvw z hz, hP z]
  ring

/-- The actual entire factor after removing the nonnegative origin order.
Its factorization is valid on all of the plane, and its growth is inherited. -/
theorem exists_entire_remove_origin_nat_with_one_sided_growth
    {v : ℂ → ℂ} {N : ℕ} (hv : Differentiable ℂ v)
    (hnz : ∀ z, z ≠ 0 → v z ≠ 0)
    (hgrowth : HasPowerExponentialBound N v) :
    ∃ m : ℕ, ∃ w : ℂ → ℂ,
      (hv.analyticAt 0).meromorphicAt.order = ((m : ℤ) : WithTop ℤ) ∧
      Differentiable ℂ w ∧ (∀ z, w z ≠ 0) ∧
      (∀ z, v z = z^m * w z) ∧ HasPowerExponentialBound N w := by
  obtain ⟨q, w, hq, hwd, hwnz, hvw, hw⟩ :=
    exists_entire_remove_origin_with_one_sided_growth (hv.analyticAt 0).meromorphicAt
      (fun z _ => hv z) hnz hgrowth
  have hq0 : 0 ≤ q := by
    have hh := (hv.analyticAt 0).meromorphicAt_order_nonneg
    rw [hq] at hh
    exact_mod_cast hh
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hq0
  refine ⟨m, w, hq, hwd, hwnz, ?_, hw⟩
  have he : v = fun z => z^m * w z := by
    apply Continuous.ext_on (dense_compl_singleton (0 : ℂ)) hv.continuous
      ((continuous_id.pow m).mul hwd.continuous)
    intro z hz
    simpa only [zpow_natCast] using hvw z (by simpa using hz)
  exact congrFun he

/-- Entire functions nonzero off zero have a natural-number origin order.
The factorization extends to zero by continuity, including the m=0 case. -/
theorem entire_eq_pow_exp_polynomial_of_one_sided_growth
    {v : ℂ → ℂ} {N : ℕ} (hN : 0 < N) (hv : Differentiable ℂ v)
    (hnz : ∀ z, z ≠ 0 → v z ≠ 0)
    (hgrowth : HasPowerExponentialBound N v) :
    ∃ m : ℕ, ∃ c : ℂ, ∃ P : Polynomial ℂ,
      (hv.analyticAt 0).meromorphicAt.order = ((m : ℤ) : WithTop ℤ) ∧
      c ≠ 0 ∧ P.coeff 0 = 0 ∧ P.natDegree ≤ N ∧
      ∀ z, v z = c * z^m * Complex.exp (P.eval z) := by
  obtain ⟨q, c, P, hq, hc, hP0, hPN, hP⟩ :=
    meromorphic_unit_eq_zpow_exp_polynomial_of_one_sided_growth hN
      (hv.analyticAt 0).meromorphicAt (fun z _ => hv z) hnz hgrowth
  have hq0 : 0 ≤ q := by
    have hh := (hv.analyticAt 0).meromorphicAt_order_nonneg
    rw [hq] at hh
    exact_mod_cast hh
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hq0
  refine ⟨m, c, P, hq, hc, hP0, hPN, ?_⟩
  have he : v = fun z => c * z^m * Complex.exp (P.eval z) := by
    apply Continuous.ext_on (dense_compl_singleton (0 : ℂ)) hv.continuous
    · exact ((continuous_const.mul (continuous_id.pow m)).mul
        (Complex.continuous_exp.comp P.continuous))
    · intro z hz
      simpa only [zpow_natCast] using hP z (by simpa using hz)
  exact congrFun he

/-- Determinant-shaped exponential-type formula. Its hypotheses are actual
entireness, nonvanishing off zero, and one-sided exponential growth. -/
theorem entire_eq_pow_exp_linear_of_one_sided_growth {v : ℂ → ℂ}
    (hv : Differentiable ℂ v) (hnz : ∀ z, z ≠ 0 → v z ≠ 0)
    (hgrowth : HasPowerExponentialBound 1 v) :
    ∃ m : ℕ, ∃ c a : ℂ,
      (hv.analyticAt 0).meromorphicAt.order = ((m : ℤ) : WithTop ℤ) ∧
      c ≠ 0 ∧ ∀ z, v z = c * z^m * Complex.exp (a*z) := by
  obtain ⟨m, c, P, hm, hc, hP0, hPN, hP⟩ :=
    entire_eq_pow_exp_polynomial_of_one_sided_growth (by decide) hv hnz hgrowth
  refine ⟨m, c, P.coeff 1, hm, hc, fun z => ?_⟩
  rw [hP z, eval_eq_coeff_one_mul_of_natDegree_le_one hP0 hPN]

/-- The reciprocal estimate is a consequence of the one-sided theorem in
exponential type. It is not a premise of the determinant-shaped argument. -/
theorem powerExponentialBound_inverse_of_entire_one_sided_growth {v : ℂ → ℂ}
    (hv : Differentiable ℂ v) (hnz : ∀ z, z ≠ 0 → v z ≠ 0)
    (hgrowth : HasPowerExponentialBound 1 v) :
    HasPowerExponentialBound 1 (fun z => (v z)⁻¹) := by
  obtain ⟨m, c, a, _, _, hformula⟩ :=
    entire_eq_pow_exp_linear_of_one_sided_growth hv hnz hgrowth
  apply powerExponentialBound_congr_exterior
    (powerExponentialBound_laurent_exp 1 id c⁻¹ (-a) (-(m : ℤ)))
  intro z hz
  simp only [id_eq, pow_one, neg_mul, Complex.exp_neg, zpow_neg, zpow_natCast,
    hformula z, mul_inv_rev]
  ring

/-- The actual reciprocal after power pullback also has the required order-N
bound, derived from the one-sided exponential-type assumptions on v. -/
theorem powerExponentialBound_inverse_power_pullback_of_entire_one_sided_growth
    {v : ℂ → ℂ} (hv : Differentiable ℂ v)
    (hnz : ∀ z, z ≠ 0 → v z ≠ 0)
    (hgrowth : HasPowerExponentialBound 1 v) (N : ℕ) :
    HasPowerExponentialBound N (fun z => (v (z^N))⁻¹) := by
  obtain ⟨m, c, a, _, _, hformula⟩ :=
    entire_eq_pow_exp_linear_of_one_sided_growth hv hnz hgrowth
  apply powerExponentialBound_congr_exterior
    (powerExponentialBound_laurent_exp N id c⁻¹ (-a) (-((N*m : ℕ) : ℤ)))
  intro z hz
  simp only [id_eq, neg_mul, Complex.exp_neg, zpow_neg, zpow_natCast,
    hformula (z^N), mul_inv_rev, pow_mul]
  ring

end StrictEUnit
#print axioms StrictEUnit.exists_entire_remove_origin_with_one_sided_growth
#print axioms StrictEUnit.meromorphic_unit_eq_zpow_exp_polynomial_of_one_sided_growth
#print axioms StrictEUnit.exists_entire_remove_origin_nat_with_one_sided_growth
#print axioms StrictEUnit.entire_eq_pow_exp_polynomial_of_one_sided_growth
#print axioms StrictEUnit.entire_eq_pow_exp_linear_of_one_sided_growth

#print axioms StrictEUnit.powerExponentialBound_inverse_of_entire_one_sided_growth
#print axioms StrictEUnit.powerExponentialBound_inverse_power_pullback_of_entire_one_sided_growth
