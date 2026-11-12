import OrdinaryPointConnectionDenominators
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
Conditional algebraic transfer of scalar binomial denominator arithmetic
through a descending-Pochhammer factor. This helper proves no factorization
for a selected operator, rationality of roots, or Frobenius representation.
-/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- The roots of the literal descending polynomial are precisely its finite
list of natural-number casts. This does not require characteristic zero. -/
theorem descPochhammer_eval_eq_zero_iff_natCast
    {K : Type*} [Field K] (s : ℕ) (ξ : K) :
    (descPochhammer K s).eval ξ = 0 ↔
      ∃ k : ℕ, k < s ∧ ξ = (k : K) := by
  classical
  rw [descPochhammer_eval_eq_prod_range, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, hk, hzero⟩
    exact ⟨k, Finset.mem_range.mp hk, sub_eq_zero.mp hzero⟩
  · rintro ⟨k, hk, hξ⟩
    exact ⟨k, Finset.mem_range.mpr hk, sub_eq_zero.mpr hξ⟩

/-- At a natural-number exponent the scalar binomial quantity is the cast
of an ordinary natural binomial coefficient, hence integral over ℤ. -/
theorem natCast_descPochhammer_div_factorial_integral
    {K : Type*} [Field K] [CharZero K] (k m : ℕ) :
    IsIntegral ℤ
      ((descPochhammer K m).eval (k : K) / (m.factorial : K)) := by
  rw [← Nat.cast_choose_eq_descPochhammer_div K k m]
  exact ordinaryJet_natCast_integral (k.choose m)

/-- Exponentially bounded positive common integer denominators for every
finite prefix of the literal scalar binomial sequence. The constant may
depend on the exponent. -/
def BinomialPrefixDenominators
    {K : Type*} [Field K] (ξ : K) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, ∃ d : ℕ,
    0 < d ∧ (d : ℝ) ≤ C ^ (N + 1) ∧
      ∀ m, m ≤ N → IsIntegral ℤ
        ((d : K) * ((descPochhammer K m).eval ξ / (m.factorial : K)))

/-- Natural-number exponents have the literal common choices C=1 and d=1
at every prefix, with no denominator loss. -/
theorem natCast_binomialPrefixDenominators
    {K : Type*} [Field K] [CharZero K] (k : ℕ) :
    BinomialPrefixDenominators (k : K) := by
  refine ⟨1, le_rfl, ?_⟩
  intro N
  refine ⟨1, Nat.zero_lt_one, ?_, ?_⟩
  · simp
  · intro m hm
    simpa only [Nat.cast_one, one_mul] using
      natCast_descPochhammer_div_factorial_integral (K := K) k m

/-- A nonzero scalar and descending-Pochhammer factor introduce only natural
integer roots. Arithmetic for roots of Q therefore transfers to every root
of P. The displayed factorization is a conditional helper input, not a
construction or a selected-operator existence premise. -/
theorem binomialPrefixDenominators_of_indicial_factorization
    {K : Type*} [Field K] [CharZero K]
    (P Q : Polynomial K) (γ : K) (s : ℕ)
    (hfactor : P = Polynomial.C γ * descPochhammer K s * Q)
    (hγ : γ ≠ 0)
    (hQ : ∀ ξ : K, Q.eval ξ = 0 → BinomialPrefixDenominators ξ) :
    ∀ ξ : K, P.eval ξ = 0 → BinomialPrefixDenominators ξ := by
  intro ξ hξ
  have hmul : γ * ((descPochhammer K s).eval ξ * Q.eval ξ) = 0 := by
    simpa only [hfactor, Polynomial.eval_mul, Polynomial.eval_C, mul_assoc] using hξ
  have hprod : (descPochhammer K s).eval ξ * Q.eval ξ = 0 :=
    (mul_eq_zero.mp hmul).resolve_left hγ
  rcases mul_eq_zero.mp hprod with hdesc | hroot
  · obtain ⟨k, hk, hcast⟩ :=
      (descPochhammer_eval_eq_zero_iff_natCast s ξ).mp hdesc
    rw [hcast]
    exact natCast_binomialPrefixDenominators k
  · exact hQ ξ hroot

end StrictEUnit
end
