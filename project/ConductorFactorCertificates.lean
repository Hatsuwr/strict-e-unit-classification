import SimpleFieldBinomialDescent

noncomputable section
attribute [local instance] Ideal.Quotient.field
attribute [local instance] Classical.propDecidable
open scoped NumberField
open UniqueFactorizationMonoid
namespace StrictEUnit

/-- The finite conductor exception set suffices for every higher-degree factor:
neither the prime ideal nor the residue equation is an extra premise. -/
theorem factor_certificate_of_conductor_exceptions
    {K : Type*} [Field K] [NumberField K]
    (a : 𝓞 K) (T : Finset ℕ)
    (hT : ∀ p : ℕ, p.Prime → p ∉ T →
      (conductor ℤ a).comap (algebraMap ℤ (𝓞 K)) ⊔ Ideal.span {(p : ℤ)} = ⊤)
    (p : ℕ) (hp : p.Prime) (hgood : p ∉ T)
    (I : Ideal ℤ) [I.IsMaximal] (hI : I = Ideal.span {(p : ℤ)})
    (Q : Polynomial ℤ)
    (hQ : Q.map (Ideal.Quotient.mk I) ∈ normalizedFactors
      ((minpoly ℤ a).map (Ideal.Quotient.mk I)))
    (hd : 1 < (Q.map (Ideal.Quotient.mk I)).degree) :
    ∃ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      w.valuation K (p : K) < 1 ∧
      ∀ j : ℕ, w.valuation K ((a : K) - (j : K)) = 1 := by
  have hpI : (p : ℤ) ∈ I := by rw [hI]; exact Ideal.subset_span (by simp)
  have hI0 : I ≠ ⊥ := by
    intro he
    rw [he, Ideal.mem_bot] at hpI
    exact (Nat.cast_ne_zero.mpr hp.ne_zero) hpI
  apply numberField_kummer_higher_degree_certificate a I hI0
    (by rw [hI]; exact hT p hp hgood) Q hQ hd p hpI

/-- Actual simple-field arithmetic and factor-place certificates share the
same generator and finite exceptional set. This does not assert factor supply. -/
theorem simpleField_binomial_factor_certificates
    {K : Type*} [Field K] [NumberField K] (a : K)
    (ha : IsIntegral ℤ a) (hb : BinomialPrefixDenominators a) :
    ∃ a' : 𝓞 (IntermediateField.adjoin ℚ {a}),
      algebraMap (IntermediateField.adjoin ℚ {a}) K (a' : IntermediateField.adjoin ℚ {a}) = a ∧
      BinomialPrefixDenominators (a' : IntermediateField.adjoin ℚ {a}) ∧
      ∃ T : Finset ℕ, ∀ (p : ℕ), p.Prime → p ∉ T →
        ∀ (I : Ideal ℤ) [I.IsMaximal], I = Ideal.span {(p : ℤ)} →
        ∀ Q : Polynomial ℤ,
          Q.map (Ideal.Quotient.mk I) ∈ normalizedFactors
            ((minpoly ℤ a').map (Ideal.Quotient.mk I)) →
          1 < (Q.map (Ideal.Quotient.mk I)).degree →
          ∃ w : IsDedekindDomain.HeightOneSpectrum (𝓞 (IntermediateField.adjoin ℚ {a})),
            w.valuation (IntermediateField.adjoin ℚ {a}) (p : IntermediateField.adjoin ℚ {a}) < 1 ∧
            ∀ j : ℕ, w.valuation (IntermediateField.adjoin ℚ {a})
              ((a' : IntermediateField.adjoin ℚ {a}) - (j : IntermediateField.adjoin ℚ {a})) = 1 := by
  obtain ⟨a', he, hbin, T, hT⟩ := simpleField_binomial_conductor_descent a ha hb
  refine ⟨a', he, hbin, T, ?_⟩
  intro p hp hgood I hmax hI Q hQ hd
  exact factor_certificate_of_conductor_exceptions a' T hT p hp hgood I hI Q hQ hd

end StrictEUnit
end
