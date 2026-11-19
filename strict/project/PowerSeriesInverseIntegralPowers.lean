import PolynomialDifferentialSubring
import Mathlib.RingTheory.PowerSeries.Inverse

/-! Integral coefficient bounds for a full inverse power-series germ.
The exponent is additive in inverse power and coefficient degree. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K]

theorem powerSeries_inverse_integral_coefficient
    (f : PowerSeries K) (tau : K) (hconst : PowerSeries.constantCoeff K f=tau)
    (htau : tau≠0) (hf : ∀ n,IsIntegral ℤ (PowerSeries.coeff K n f)) :
    ∀ n,IsIntegral ℤ (tau^(n+1)*PowerSeries.coeff K n f⁻¹) := by
  have ht : IsIntegral ℤ tau := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply,hconst] using hf 0
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [PowerSeries.coeff_inv,hconst]
    by_cases hn : n=0
    · rw [hn,if_pos rfl,pow_one,mul_inv_cancel₀ htau]
      exact isIntegral_one
    · rw [if_neg hn]
      have halg (s : K) : tau^(n+1)*(-tau⁻¹*s)=-(tau^n*s) := by
        rw [pow_succ]
        calc
          _ = -(tau^n*(tau*tau⁻¹)*s) := by ring
          _ = _ := by rw [mul_inv_cancel₀ htau,mul_one]
      rw [halg,Finset.mul_sum]
      apply IsIntegral.neg
      apply IsIntegral.sum
      intro ij hij
      by_cases hj : ij.2<n
      · rw [if_pos hj]
        have he : n=(n-(ij.2+1))+(ij.2+1) := by omega
        have h := ((ht.pow (n-(ij.2+1))).mul (hf ij.1)).mul (ih ij.2 hj)
        convert h using 1
        nth_rw 1 [he]
        rw [pow_add]
        ring
      · rw [if_neg hj,mul_zero]
        exact isIntegral_zero

theorem powerSeries_inverse_pow_integral_coefficient
    (f : PowerSeries K) (tau : K) (hconst : PowerSeries.constantCoeff K f=tau)
    (htau : tau≠0) (hf : ∀ n,IsIntegral ℤ (PowerSeries.coeff K n f)) :
    ∀ m n,IsIntegral ℤ (tau^(m+n)*PowerSeries.coeff K n ((f⁻¹)^m)) := by
  intro m
  induction m with
  | zero =>
    intro n
    simp only [pow_zero,PowerSeries.coeff_one]
    split_ifs with hn
    · subst n
      simp only [Nat.add_zero,pow_zero,one_mul]
      exact isIntegral_one
    · rw [mul_zero]
      exact isIntegral_zero
  | succ m ih =>
    intro n
    rw [pow_succ,PowerSeries.coeff_mul,Finset.mul_sum]
    apply IsIntegral.sum
    intro ij hij
    have he : ij.1+ij.2=n := Finset.mem_antidiagonal.mp hij
    have h := (ih ij.1).mul (powerSeries_inverse_integral_coefficient f tau hconst htau hf ij.2)
    convert h using 1
    rw [← mul_mul_mul_comm,← pow_add]
    congr 2
    omega

theorem powerSeries_cleared_mul_inverse_pow_integral
    (f g : PowerSeries K) (tau delta : K)
    (hconst : PowerSeries.constantCoeff K f=tau) (htau : tau≠0)
    (hf : ∀ n,IsIntegral ℤ (PowerSeries.coeff K n f))
    (hg : ∀ n,IsIntegral ℤ (delta*PowerSeries.coeff K n g)) (m n : ℕ) :
    IsIntegral ℤ (delta*tau^(m+n)*PowerSeries.coeff K n (g*(f⁻¹)^m)) := by
  have ht : IsIntegral ℤ tau := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply,hconst] using hf 0
  rw [PowerSeries.coeff_mul,Finset.mul_sum]
  apply IsIntegral.sum
  intro ij hij
  have he : ij.1+ij.2=n := Finset.mem_antidiagonal.mp hij
  have h := ((ht.pow ij.1).mul (hg ij.1)).mul
    (powerSeries_inverse_pow_integral_coefficient f tau hconst htau hf m ij.2)
  convert h using 1
  have hp : tau^(m+n)=tau^ij.1*tau^(m+ij.2) := by rw [← pow_add]; congr 1; omega
  rw [hp]
  ring

end StrictEUnit
end
