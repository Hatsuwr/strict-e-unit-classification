import EntireLogarithm
import RealPartPolynomialGrowth
import RingExpressionGrowth

/-! Actual two-sided exterior growth of a zero-free entire function implies
an exponential polynomial. The analytic function and its bounds are inputs;
no identification with the formal PV candidate or numerical values is asserted. -/
noncomputable section
namespace StrictEUnit

lemma log_norm_le_of_power_exponential_bound {w : ℂ → ℂ} {N : ℕ}
    (hN : 0 < N) (hnz : ∀ z, w z ≠ 0) (hw : HasPowerExponentialBound N w) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z, 1 ≤ ‖z‖ → Real.log ‖w z‖ ≤ D * ‖z‖^N := by
  obtain ⟨C,hC,M,hb⟩ := hw
  refine ⟨2*C+M, by positivity, ?_⟩
  intro z hz
  have hr : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one hz
  have hp : 0 < 1+‖z‖ := by positivity
  have hh := Real.log_le_log (norm_pos_iff.mpr (hnz z)) (hb z hz)
  simp only [id_eq] at hh
  rw [Real.log_mul (ne_of_gt (mul_pos hC (pow_pos hp _))) (Real.exp_ne_zero _),
    Real.log_mul hC.ne' (pow_ne_zero _ hp.ne'), Real.log_pow, Real.log_exp] at hh
  have hlogC : Real.log C ≤ C := Real.log_le_self hC.le
  have hlogr : Real.log (1+‖z‖) ≤ ‖z‖ := by
    have h := Real.log_le_sub_one_of_pos hp
    linarith
  have hrN : ‖z‖ ≤ ‖z‖^N := le_self_pow₀ hz hN.ne'
  have h1 : 1 ≤ ‖z‖^N := one_le_pow₀ hz
  have hCp := mul_le_mul_of_nonneg_left h1 hC.le
  have hMp := mul_le_mul_of_nonneg_left (hlogr.trans hrN) (Nat.cast_nonneg M : (0:ℝ)≤M)
  nlinarith

/-- The real-part bound is derived from bounds on w and its reciprocal,
using the actual normalized logarithm identity. -/
theorem real_part_bound_of_unit_growth {w g : ℂ → ℂ} {N : ℕ}
    (hN : 0 < N) (hnz : ∀ z, w z ≠ 0)
    (hlog : ∀ z, w z = w 0 * Complex.exp (g z))
    (hw : HasPowerExponentialBound N w)
    (hi : HasPowerExponentialBound N (fun z => (w z)⁻¹)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, 1 ≤ ‖z‖ → |(g z).re| ≤ C*‖z‖^N + C := by
  obtain ⟨D,hD,hDw⟩ := log_norm_le_of_power_exponential_bound hN hnz hw
  obtain ⟨E,hE,hEi⟩ := log_norm_le_of_power_exponential_bound hN
    (fun z => inv_ne_zero (hnz z)) hi
  let K := Real.log ‖w 0‖
  refine ⟨D+E+|K|, by positivity, ?_⟩
  intro z hz
  have he : Real.log ‖w z‖ = K + (g z).re := by
    rw [hlog z, norm_mul, Complex.norm_exp, Real.log_mul (norm_ne_zero_iff.mpr (hnz 0))
      (Real.exp_ne_zero _), Real.log_exp]
  have hu := hDw z hz
  have hl := hEi z hz
  rw [norm_inv, Real.log_inv, he] at hl
  rw [he] at hu
  have hp : 0 ≤ ‖z‖^N := pow_nonneg (norm_nonneg _) _
  have hd : 0 ≤ D*‖z‖^N := mul_nonneg hD hp
  have he' : 0 ≤ E*‖z‖^N := mul_nonneg hE hp
  have hk : 0 ≤ |K| *‖z‖^N := mul_nonneg (abs_nonneg _) hp
  have hka := le_abs_self K
  have hkb := neg_abs_le K
  apply abs_le.mpr
  constructor <;> nlinarith [abs_nonneg K]

/-- A genuine entire unit with actual two-sided power-exponential growth is
its value at zero times exp(P), with P(0)=0 and degree at most N. -/
theorem entire_unit_eq_exp_polynomial {w : ℂ → ℂ} {N : ℕ}
    (hN : 0 < N) (hw : Differentiable ℂ w) (hnz : ∀ z, w z ≠ 0)
    (hgrowth : HasPowerExponentialBound N w)
    (hinv : HasPowerExponentialBound N (fun z => (w z)⁻¹)) :
    ∃ P : Polynomial ℂ, P.coeff 0 = 0 ∧ P.natDegree ≤ N ∧
      (∀ z, w z = w 0 * Complex.exp (P.eval z)) ∧
      ∀ z, HasDerivAt (fun t => P.eval t) (deriv w z / w z) z := by
  obtain ⟨g,hg0,hg,hgd,hlog⟩ := exists_normalized_entire_logarithm hw hnz
  obtain ⟨C,hC,hbound⟩ := real_part_bound_of_unit_growth hN hnz hlog hgrowth hinv
  obtain ⟨P,hP,hdegree⟩ := entire_polynomial_of_exterior_real_part_growth hg hg0 C 0 hC
    (le_refl 0) N hN (fun z hz => by simpa using hbound z hz)
  refine ⟨P, ?_, hdegree, ?_, ?_⟩
  · simpa [hg0, Polynomial.coeff_zero_eq_eval_zero] using hP 0
  · intro z
    rw [hP]
    exact hlog z
  · have he : (fun z => P.eval z) = g := funext hP
    rw [he]
    exact hgd
end StrictEUnit
#print axioms StrictEUnit.log_norm_le_of_power_exponential_bound
#print axioms StrictEUnit.real_part_bound_of_unit_growth
#print axioms StrictEUnit.entire_unit_eq_exp_polynomial
