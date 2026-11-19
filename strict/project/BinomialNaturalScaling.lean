import NonsplitFactorSelection

noncomputable section
open scoped BigOperators NumberField
namespace StrictEUnit

/-- Vandermonde convolution preserves exponentially bounded common
binomial denominators, using the product of the two clearing integers. -/
theorem binomialPrefixDenominators_add
    {K : Type*} [Field K] [CharZero K] (a b : K)
    (ha : BinomialPrefixDenominators a) (hb : BinomialPrefixDenominators b) :
    BinomialPrefixDenominators (a + b) := by
  obtain ⟨A, hA, hda⟩ := ha
  obtain ⟨B, hB, hdb⟩ := hb
  refine ⟨A * B, one_le_mul_of_one_le_of_one_le hA hB, ?_⟩
  intro N
  obtain ⟨d, hd, hAd, hid⟩ := hda N
  obtain ⟨e, he, hBe, hie⟩ := hdb N
  refine ⟨d * e, Nat.mul_pos hd he, ?_, ?_⟩
  · rw [Nat.cast_mul, mul_pow]
    exact mul_le_mul hAd hBe (Nat.cast_nonneg e) (pow_nonneg (le_trans zero_le_one hA) _)
  · intro m hm
    rw [← field_choose_eq_descPochhammer_div, Ring.add_choose_eq m (Commute.all a b),
      Finset.mul_sum]
    apply IsIntegral.sum
    intro ij hij
    have hi := (hid ij.1 ((Finset.antidiagonal.fst_le hij).trans hm)).mul
      (hie ij.2 ((Finset.antidiagonal.snd_le hij).trans hm))
    rw [← field_choose_eq_descPochhammer_div, ← field_choose_eq_descPochhammer_div] at hi
    convert hi using 1 <;> push_cast <;> ring

/-- Positive integer scaling introduces no new arithmetic hypothesis. -/
theorem binomialPrefixDenominators_nat_mul
    {K : Type*} [Field K] [CharZero K] (a : K)
    (ha : BinomialPrefixDenominators a) (n : ℕ) :
    BinomialPrefixDenominators ((n : K) * a) := by
  induction n with
  | zero => simpa using (natCast_binomialPrefixDenominators (K := K) 0)
  | succ n ih =>
    simpa [Nat.cast_add, add_mul] using binomialPrefixDenominators_add _ _ ih ha

/-- The first binomial coefficient itself provides a positive integral
multiple; scaling closure retains the entire prefix arithmetic. -/
theorem binomialPrefixDenominators_exists_integral_multiple
    {K : Type*} [Field K] [CharZero K] (a : K)
    (ha : BinomialPrefixDenominators a) :
    ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : K) * a) ∧
      BinomialPrefixDenominators ((n : K) * a) := by
  obtain ⟨C, hC, hden⟩ := ha
  obtain ⟨n, hn, _, hi⟩ := hden 1
  refine ⟨n, hn, ?_, binomialPrefixDenominators_nat_mul a ⟨C, hC, hden⟩ n⟩
  have h := hi 1 le_rfl
  rw [← field_choose_eq_descPochhammer_div, Ring.choose_one_right] at h
  exact h

/-- Rationality of the integral case would suffice for all exponents.
This is a reduction, not an assertion of that still-open case. -/
theorem binomial_rationality_of_integral_case
    {K : Type*} [Field K] [CharZero K]
    (H : ∀ b : K, IsIntegral ℤ b → BinomialPrefixDenominators b →
      ∃ q : ℚ, b = (q : K))
    (a : K) (ha : BinomialPrefixDenominators a) :
    ∃ q : ℚ, a = (q : K) := by
  obtain ⟨n, hn, hi, hb⟩ := binomialPrefixDenominators_exists_integral_multiple a ha
  obtain ⟨q, hq⟩ := H _ hi hb
  refine ⟨q / (n : ℚ), ?_⟩
  push_cast
  apply (eq_div_iff (Nat.cast_ne_zero.mpr (ne_of_gt hn))).mpr
  simpa only [mul_comm] using hq

/-- Original arithmetic supplies an integral scaled generator whose actual
simple field has the already-proved conductor and binomial data. -/
theorem binomial_scaled_simpleField_conductor
    {K : Type*} [Field K] [NumberField K] (a : K)
    (ha : BinomialPrefixDenominators a) :
    ∃ n : ℕ, 0 < n ∧
      ∃ a' : 𝓞 (IntermediateField.adjoin ℚ {((n : K) * a)}),
        algebraMap (IntermediateField.adjoin ℚ {((n : K) * a)}) K
          (a' : IntermediateField.adjoin ℚ {((n : K) * a)}) = (n : K) * a ∧
        BinomialPrefixDenominators
          (a' : IntermediateField.adjoin ℚ {((n : K) * a)}) ∧
        ∃ T : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ T →
          (conductor ℤ a').comap
            (algebraMap ℤ (𝓞 (IntermediateField.adjoin ℚ {((n : K) * a)}))) ⊔
            Ideal.span {(p : ℤ)} = ⊤ := by
  obtain ⟨n, hn, hi, hb⟩ := binomialPrefixDenominators_exists_integral_multiple a ha
  exact ⟨n, hn, simpleField_binomial_conductor_descent _ hi hb⟩

end StrictEUnit
end
