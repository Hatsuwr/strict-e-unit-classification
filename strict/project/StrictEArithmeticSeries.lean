import StrictEArithmeticClosure
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Factorial-series addition and multiplication

The product coefficients are the actual binomial convolution. Absolute
convergence is derived from strict arithmetic bounds, rather than assumed.
These lemmas establish the analytic series identities, not ODE closure.
-/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- Full strict arithmetic supplies absolute convergence at every point. -/
theorem strictEArithmetic_egf_summable_norm {a : ℕ → AlgebraicComplex}
    (ha : HasStrictEArithmetic a) (z : ℂ) :
    Summable (fun n : ℕ => ‖(a n : ℂ) * z ^ n / (n.factorial : ℂ)‖) := by
  obtain ⟨C, _, hbound⟩ := strictEArithmetic_chosen_bound ha
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (geometric_egf_term_norm_le (fun n => (a n : ℂ)) C hbound z)
    (geometric_egf_majorant_hasSum C z).summable

/-- Addition of the actual factorial-normalized series. -/
theorem strictE_egf_hasSum_add {a b : ℕ → AlgebraicComplex} {u v z : ℂ}
    (ha : HasSum (fun n => (a n : ℂ) * z ^ n / (n.factorial : ℂ)) u)
    (hb : HasSum (fun n => (b n : ℂ) * z ^ n / (n.factorial : ℂ)) v) :
    HasSum (fun n => ((a n + b n : AlgebraicComplex) : ℂ) * z ^ n /
      (n.factorial : ℂ)) (u + v) := by
  simpa only [IntermediateField.coe_add, add_mul, add_div] using ha.add hb

/-- Negation of the actual factorial-normalized series. -/
theorem strictE_egf_hasSum_neg {a : ℕ → AlgebraicComplex} {u z : ℂ}
    (ha : HasSum (fun n => (a n : ℂ) * z ^ n / (n.factorial : ℂ)) u) :
    HasSum (fun n => ((-a n : AlgebraicComplex) : ℂ) * z ^ n /
      (n.factorial : ℂ)) (-u) := by
  simpa only [IntermediateField.coe_neg, neg_mul, neg_div] using ha.neg

/-- Algebraic scalar multiplication of the factorial-normalized series. -/
theorem strictE_egf_hasSum_const_mul {a : ℕ → AlgebraicComplex} {u z : ℂ}
    (ha : HasSum (fun n => (a n : ℂ) * z ^ n / (n.factorial : ℂ)) u)
    (α : AlgebraicComplex) :
    HasSum (fun n => ((α * a n : AlgebraicComplex) : ℂ) * z ^ n /
      (n.factorial : ℂ)) ((α : ℂ) * u) := by
  simpa only [IntermediateField.coe_mul, mul_assoc, mul_div_assoc] using ha.mul_left (α : ℂ)

/-- The finite binomial identity with all factorial denominators. -/
theorem strictE_binomial_egf_term (a b : ℕ → ℂ) (z : ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * a k * b (n - k)) * z ^ n /
      (n.factorial : ℂ) =
    ∑ k ∈ Finset.range (n + 1),
      (a k * z ^ k / (k.factorial : ℂ)) *
      (b (n - k) * z ^ (n - k) / ((n - k).factorial : ℂ)) := by
  rw [Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [Nat.cast_choose ℂ hkn]
  have hz : z ^ n = z ^ k * z ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_of_le hkn]
  rw [hz]
  calc
    _ = ((n.factorial : ℂ) / (n.factorial : ℂ)) *
        ((a k * z ^ k / (k.factorial : ℂ)) *
          (b (n - k) * z ^ (n - k) / ((n - k).factorial : ℂ))) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [div_self hfac, one_mul]

/-- The product of two actual strict-arithmetic factorial series has precisely
its binomial-convolution series, with no extra convergence assumption. -/
theorem strictE_egf_hasSum_mul {a b : ℕ → AlgebraicComplex} {u v z : ℂ}
    (ha : HasStrictEArithmetic a) (hb : HasStrictEArithmetic b)
    (hsa : HasSum (fun n => (a n : ℂ) * z ^ n / (n.factorial : ℂ)) u)
    (hsb : HasSum (fun n => (b n : ℂ) * z ^ n / (n.factorial : ℂ)) v) :
    HasSum (fun n => (strictEBinomialConvolution a b n : ℂ) * z ^ n /
      (n.factorial : ℂ)) (u * v) := by
  have h := hasSum_sum_range_mul_of_summable_norm
    (strictEArithmetic_egf_summable_norm ha z) (strictEArithmetic_egf_summable_norm hb z)
  rw [hsa.tsum_eq, hsb.tsum_eq] at h
  convert h using 1
  funext n
  change (algebraicClosure ℚ ℂ).val (strictEBinomialConvolution a b n) * z ^ n /
    (n.factorial : ℂ) = _
  simpa only [strictEBinomialConvolution, map_sum, map_mul, map_natCast] using
    strictE_binomial_egf_term (fun k => (a k : ℂ)) (fun k => (b k : ℂ)) z n

end StrictEUnit

#print axioms StrictEUnit.strictEArithmetic_egf_summable_norm
#print axioms StrictEUnit.strictE_egf_hasSum_add
#print axioms StrictEUnit.strictE_egf_hasSum_neg
#print axioms StrictEUnit.strictE_egf_hasSum_const_mul
#print axioms StrictEUnit.strictE_binomial_egf_term
#print axioms StrictEUnit.strictE_egf_hasSum_mul
