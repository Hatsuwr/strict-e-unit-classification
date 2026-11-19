import PowerBasisConductor

noncomputable section
open scoped NumberField
namespace StrictEUnit

/-- Literal binomial denominator arithmetic reflects along a field embedding
with the same denominator and growth constant. -/
theorem binomialPrefixDenominators_of_map
    {K L : Type*} [Field K] [Field L] [CharZero K] [CharZero L]
    (f : K →+* L) (a : K) (h : BinomialPrefixDenominators (f a)) :
    BinomialPrefixDenominators a := by
  obtain ⟨C, hC, hden⟩ := h
  refine ⟨C, hC, ?_⟩
  intro N
  obtain ⟨d, hd, hdb, hi⟩ := hden N
  refine ⟨d, hd, hdb, ?_⟩
  intro m hm
  rw [← field_choose_eq_descPochhammer_div]
  apply (isIntegral_algHom_iff f.toIntAlgHom f.injective).mp
  change IsIntegral ℤ (f ((d : K) * Ring.choose a m))
  rw [map_mul, map_natCast, field_choose_map, field_choose_eq_descPochhammer_div]
  exact hi m hm

/-- The same actual alpha, binomial arithmetic, and finite conductor exceptions
live together in Q(alpha). Integrality remains an explicit hypothesis. -/
theorem simpleField_binomial_conductor_descent
    {K : Type*} [Field K] [NumberField K] (a : K)
    (ha : IsIntegral ℤ a) (hb : BinomialPrefixDenominators a) :
    ∃ a' : 𝓞 (IntermediateField.adjoin ℚ {a}),
      algebraMap (IntermediateField.adjoin ℚ {a}) K (a' : IntermediateField.adjoin ℚ {a}) = a ∧
      BinomialPrefixDenominators (a' : IntermediateField.adjoin ℚ {a}) ∧
      ∃ T : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ T →
        (conductor ℤ a').comap (algebraMap ℤ (𝓞 (IntermediateField.adjoin ℚ {a}))) ⊔
          Ideal.span {(p : ℤ)} = ⊤ := by
  obtain ⟨a', he, T, hT⟩ := simpleField_conductor_finite_exceptions a ha
  refine ⟨a', he, ?_, T, hT⟩
  apply binomialPrefixDenominators_of_map
    (algebraMap (IntermediateField.adjoin ℚ {a}) K)
  rwa [he]

end StrictEUnit
end
