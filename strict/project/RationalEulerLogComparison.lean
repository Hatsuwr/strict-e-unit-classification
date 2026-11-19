import PrimeComplementConstraint
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

noncomputable section
open scoped BigOperators Topology
open Finset Filter
namespace StrictEUnit

theorem neg_log_one_sub_quadratic_upper {x : ℝ} (hx : 0 ≤ x) (hx2 : x ≤ 1/2) :
    -Real.log (1-x) ≤ x + 2*x^2 := by
  have hpos : 0 < 1-x := by linarith
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at h
  apply h.trans
  apply (sub_le_iff_le_add).mpr
  rw [inv_eq_one_div]
  apply (div_le_iff₀ hpos).mpr
  nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ 1-2*x by linarith)]

theorem prime_reciprocal_rpow_le_half (p : Nat.Primes) {s : ℝ} (hs : 1 ≤ s) :
    1 / (p : ℝ)^s ≤ 1/2 := by
  apply (reciprocal_rpow_le_reciprocal p.prop.one_lt.le hs).trans
  apply one_div_le_one_div_of_le (by norm_num)
  exact_mod_cast p.prop.two_le

theorem prime_reciprocal_rpow_summable {s : ℝ} (hs : 1 < s) :
    Summable (fun p : Nat.Primes => 1 / (p : ℝ)^s) :=
  (Real.summable_one_div_nat_rpow.mpr hs).subtype Nat.Prime

theorem rational_zeta_log_euler {s : ℝ} (hs : 1 < s) :
    Real.log (∑' n : ℕ, 1 / (n : ℝ)^s) =
      ∑' p : Nat.Primes, -Real.log (1 - 1 / (p : ℝ)^s) := by
  have he := riemannZeta_eulerProduct_exp_log (s := (s : ℂ)) (by simpa using hs)
  have hterm (p : Nat.Primes) :
      -Complex.log (1 - (p : ℂ)^(-(s : ℂ))) =
      ((-Real.log (1 - 1 / (p : ℝ)^s) : ℝ) : ℂ) := by
    rw [Complex.cpow_neg, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg (p : ℕ))]
    rw [← Complex.ofReal_inv, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      ← Complex.ofReal_log (by have h := prime_reciprocal_rpow_le_half p hs.le; simp only [one_div] at h; linarith),
      ← Complex.ofReal_neg]
    simp only [one_div]
  simp_rw [hterm] at he
  rw [← Complex.ofReal_tsum, ← Complex.ofReal_exp,
    zeta_eq_tsum_one_div_nat_cpow (by simpa using hs)] at he
  have hright : (∑' n : ℕ, 1 / (n : ℂ)^(s : ℂ)) =
      (((∑' n : ℕ, 1 / (n : ℝ)^s) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]
  rw [hright] at he
  have hre := Complex.ofReal_injective he
  rw [← hre, Real.log_exp]

theorem rational_zeta_log_le_prime_sum {s : ℝ} (hs : 1 < s) :
    Real.log (∑' n : ℕ, 1 / (n : ℝ)^s) ≤
      (∑' p : Nat.Primes, 1 / (p : ℝ)^s) + 2 * (∑' n : ℕ, 1 / (n : ℝ)^2) := by
  have hN : Summable (fun n : ℕ => 1 / (n : ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hP := hN.subtype Nat.Prime
  have hsq (p : Nat.Primes) : (1 / (p : ℝ)^s)^2 ≤ 1 / (p : ℝ)^2 := by
    have h := (sq_le_sq₀ (by positivity : 0 ≤ 1 / (p : ℝ)^s)
      (by positivity : 0 ≤ 1 / (p : ℝ))).mpr
        (reciprocal_rpow_le_reciprocal p.prop.one_lt.le hs.le)
    simpa only [one_div_pow] using h
  have hsqS := Summable.of_nonneg_of_le (fun p : Nat.Primes => sq_nonneg (1 / (p : ℝ)^s)) hsq hP
  have hprime := prime_reciprocal_rpow_summable hs
  have hmajor := hprime.add (hsqS.mul_left 2)
  have hlognonneg (p : Nat.Primes) : 0 ≤ -Real.log (1 - 1 / (p : ℝ)^s) := by
    apply neg_nonneg.mpr
    apply Real.log_nonpos
    · have h := prime_reciprocal_rpow_le_half p hs.le; linarith
    · have h : 0 ≤ 1 / (p : ℝ)^s := by positivity
      linarith
  have hlogle (p : Nat.Primes) := neg_log_one_sub_quadratic_upper
    (by positivity : 0 ≤ 1 / (p : ℝ)^s) (prime_reciprocal_rpow_le_half p hs.le)
  have hlogs := Summable.of_nonneg_of_le hlognonneg hlogle hmajor
  rw [rational_zeta_log_euler hs]
  calc
    _ ≤ ∑' p : Nat.Primes, (1 / (p : ℝ)^s + 2*(1 / (p : ℝ)^s)^2) :=
      hlogs.tsum_le_tsum hlogle hmajor
    _ = (∑' p : Nat.Primes, 1 / (p : ℝ)^s) + 2*(∑' p : Nat.Primes, (1 / (p : ℝ)^s)^2) := by
      rw [hprime.tsum_add (hsqS.mul_left 2), tsum_mul_left]
    _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_left
      ((hsqS.tsum_le_tsum hsq hP).trans (hN.tsum_subtype_le _ _ (fun n => by positivity)))
      (by norm_num)) _

end StrictEUnit
end
