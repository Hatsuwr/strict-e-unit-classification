import EntirePolynomialGrowth
import Mathlib.Analysis.Complex.Schwarz

/-! A genuine real-part-to-modulus estimate using Schwarz's lemma, followed
by actual entire polynomial reconstruction. No Fourier bound is assumed. -/
noncomputable section
open Complex Metric Set
namespace StrictEUnit

lemma norm_lt_norm_two_mul_sub_of_re_lt {w : ℂ} {M : ℝ}
    (hM : 0 < M) (hw : w.re < M) : ‖w‖ < ‖(2 * M : ℂ) - w‖ := by
  apply (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  norm_num at *
  nlinarith [mul_pos hM (sub_pos.mpr hw)]

/-- A normalized holomorphic function whose real part is below M on the
radius-2r disk has modulus at most 2M on the radius-r closed disk. -/
theorem norm_le_two_mul_of_re_lt_on_double_ball {f : ℂ → ℂ} {r M : ℝ}
    (hr : 0 < r) (hM : 0 < M) (hf : DifferentiableOn ℂ f (ball 0 (2*r)))
    (hf0 : f 0 = 0) (hre : ∀ z ∈ ball (0:ℂ) (2*r), (f z).re < M)
    {z : ℂ} (hz : ‖z‖ ≤ r) : ‖f z‖ ≤ 2*M := by
  let g : ℂ → ℂ := fun w => f w / ((2*M:ℂ) - f w)
  have hden : ∀ w ∈ ball (0:ℂ) (2*r), (2*M:ℂ) - f w ≠ 0 := by
    intro w hw
    have hh := norm_lt_norm_two_mul_sub_of_re_lt hM (hre w hw)
    intro he
    rw [he, norm_zero] at hh
    exact (not_lt_of_ge (norm_nonneg _)) hh
  have hg : DifferentiableOn ℂ g (ball 0 (2*r)) :=
    hf.div ((differentiableOn_const _).sub hf) hden
  have hg0 : g 0 = 0 := by simp [g, hf0]
  have hm : MapsTo g (ball 0 (2*r)) (ball (g 0) 1) := by
    intro w hw
    rw [hg0, mem_ball_zero_iff]
    dsimp [g]
    rw [norm_div, div_lt_one (norm_pos_iff.mpr (hden w hw))]
    exact norm_lt_norm_two_mul_sub_of_re_lt hM (hre w hw)
  have hzball : z ∈ ball (0:ℂ) (2*r) := by
    rw [mem_ball_zero_iff]
    linarith
  have hsch := Complex.dist_le_div_mul_dist_of_mapsTo_ball hg hm hzball
  have hhalf : ‖g z‖ ≤ (1:ℝ)/2 := by
    simp only [hg0, dist_zero_right] at hsch
    calc
      ‖g z‖ ≤ (1 / (2*r))*‖z‖ := hsch
      _ ≤ (1 / (2*r))*r := mul_le_mul_of_nonneg_left hz (by positivity)
      _ = 1/2 := by field_simp; ring
  have hmul : ‖f z‖ ≤ (1/2:ℝ) * ‖(2*M:ℂ)-f z‖ := by
    apply (div_le_iff₀ (norm_pos_iff.mpr (hden z hzball))).mp
    simpa only [g, norm_div] using hhalf
  have htriangle := norm_sub_le (2*M:ℂ) (f z)
  have hnorm : ‖(2*M:ℂ)‖ = 2*M := by
    simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]
  rw [hnorm] at htriangle
  linarith
/-- A real-part bound on expanding disks gives an actual polynomial.
The bound is on real parts only, not on the function's modulus or coefficients. -/
theorem entire_polynomial_of_real_part_disk_growth {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hf0 : f 0 = 0) (C M : ℝ) (N : ℕ)
    (hre : ∀ r : ℝ, 1 ≤ r → ∀ z : ℂ, ‖z‖ < 2*r →
      (f z).re < C*r^N + M*Real.log r + C) :
    ∃ P : Polynomial ℂ, (∀ z : ℂ, P.eval z = f z) ∧ P.natDegree ≤ N := by
  apply entire_polynomial_of_modulus_growth hf (2*C) (2*M) N
  intro z hz
  have hr : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one hz
  have hM : 0 < C*‖z‖^N + M*Real.log ‖z‖ + C := by
    have hh := hre ‖z‖ hz 0 (by simpa using mul_pos (by norm_num : (0:ℝ)<2) hr)
    simpa [hf0] using hh
  have hh := norm_le_two_mul_of_re_lt_on_double_ball hr hM hf.differentiableOn hf0
    (fun w hw => hre ‖z‖ hz w (by simpa [mem_ball_zero_iff] using hw)) (le_refl ‖z‖)
  convert hh using 1; ring

/-- In particular, a normalized entire function with a global one-sided
polynomial real-part bound is polynomial of the corresponding degree. -/
theorem entire_polynomial_of_real_part_growth {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hf0 : f 0 = 0) (C : ℝ) (hC : 0 ≤ C) (N : ℕ)
    (hre : ∀ z : ℂ, (f z).re ≤ C*(1+‖z‖)^N) :
    ∃ P : Polynomial ℂ, (∀ z : ℂ, P.eval z = f z) ∧ P.natDegree ≤ N := by
  apply entire_polynomial_of_real_part_disk_growth hf hf0 (C*3^N+1) 0 N
  intro r hr z hz
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hp : (1+‖z‖)^N ≤ (3*r)^N := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hh := (hre z).trans (mul_le_mul_of_nonneg_left hp hC)
  rw [mul_pow] at hh
  have hpow : 0 ≤ r^N := pow_nonneg hr0 N
  have hc3 : 0 ≤ C*3^N := mul_nonneg hC (by positivity)
  simp only [zero_mul, add_zero]
  nlinarith

/-- The manuscript's exterior real-part estimate suffices (N positive).
Continuity supplies the missing compact-disk bound; the logarithmic term is
absorbed into polynomial growth. No coefficient estimate is supplied. -/
theorem entire_polynomial_of_exterior_real_part_growth {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hf0 : f 0 = 0) (C M : ℝ)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (N : ℕ) (hN : 0 < N)
    (hre : ∀ z : ℂ, 1 ≤ ‖z‖ → |(f z).re| ≤ C*‖z‖^N + M*Real.log ‖z‖ + C) :
    ∃ P : Polynomial ℂ, (∀ z : ℂ, P.eval z = f z) ∧ P.natDegree ≤ N := by
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0:ℂ) 1).exists_bound_of_continuousOn hf.continuous.continuousOn
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
    have hh := (le_abs_self (f z).re).trans (hre z hz)
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

end StrictEUnit
#print axioms StrictEUnit.norm_lt_norm_two_mul_sub_of_re_lt
#print axioms StrictEUnit.norm_le_two_mul_of_re_lt_on_double_ball

#print axioms StrictEUnit.entire_polynomial_of_real_part_disk_growth
#print axioms StrictEUnit.entire_polynomial_of_real_part_growth

#print axioms StrictEUnit.entire_polynomial_of_exterior_real_part_growth
