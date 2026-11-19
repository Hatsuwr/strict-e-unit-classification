import BinomialIndividualInverseBounds
import IntegerBinomialSharedInverse

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Exact fixed-endpoint factorization. No inversion or nonvanishing is
assumed here, so it remains valid at integer collisions. -/
theorem diagonal_choose_endpoint_factorization (x : K) (N n : ℕ) (hn : n≤N) :
    ((N.choose n : ℕ) : K)*Ring.choose (x+(N : K)) N =
      Ring.choose (x+(N : K)) (N-n)*Ring.choose (x+(n : K)) n := by
  have h := Ring.choose_smul_choose (x+(N : K)) (Nat.sub_le N n)
  have hs : x+(N : K)-((N-n : ℕ) : K)=x+(n : K) := by
    rw [Nat.cast_sub hn];ring
  simpa only [nsmul_eq_mul,Nat.choose_symm hn,Nat.sub_sub_self hn,hs] using h

/-- All diagonal pivots are nonzero if x is not an integer. -/
theorem diagonal_choose_nonzero_of_noninteger (x : K)
    (hx : ∀ z : ℤ,x≠(z : K)) (n : ℕ) : Ring.choose (x+(n : K)) n≠0 := by
  rw [field_choose_eq_descPochhammer_div]
  apply div_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  rw [descPochhammer_eval_eq_prod_range]
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk he
  apply hx ((k : ℤ)-(n : ℤ))
  push_cast
  linear_combination he

/-- A single inverse at N controls every earlier inverse. Nonzero endpoint
is essential: negative integer collisions are not silently inverted. -/
theorem diagonal_choose_inverse_from_endpoint (x : K) (N n : ℕ) (hn : n≤N)
    (hN : Ring.choose (x+(N : K)) N≠0) :
    (Ring.choose (x+(n : K)) n)⁻¹ =
      Ring.choose (x+(N : K)) (N-n)*((N.choose n : ℕ) : K)⁻¹*
        (Ring.choose (x+(N : K)) N)⁻¹ := by
  have hc : ((N.choose n : ℕ) : K)≠0 := Nat.cast_ne_zero.mpr (ne_of_gt (Nat.choose_pos hn))
  have h := diagonal_choose_endpoint_factorization x N n hn
  have hnz : Ring.choose (x+(n : K)) n≠0 := by
    intro hz
    rw [hz,mul_zero] at h
    exact mul_ne_zero hc hN h
  field_simp
  linear_combination h

end StrictEUnit
end
