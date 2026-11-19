import ConductorFactorCertificates

noncomputable section
attribute [local instance] Ideal.Quotient.field
attribute [local instance] Classical.propDecidable
open UniqueFactorizationMonoid
open scoped NumberField
namespace StrictEUnit

/-- Failure to split supplies an actual higher-degree normalized factor. -/
theorem nonsplit_exists_higher_normalized_factor
    {F : Type*} [Field F] (P : Polynomial F)
    (hn : ¬ P.Splits (RingHom.id F)) :
    ∃ g ∈ normalizedFactors P, 1 < g.degree := by
  classical
  have hP0 : P ≠ 0 := by intro h; subst P; exact hn (Polynomial.splits_zero _)
  by_contra h
  push_neg at h
  apply hn
  rw [Polynomial.splits_iff]
  right
  intro g hg hdiv
  simp only [Polynomial.map_id] at hdiv
  obtain ⟨q, hq, hassoc⟩ := exists_mem_normalizedFactors_of_dvd hP0 hg hdiv
  have hle : g.degree ≤ 1 := by
    rw [Polynomial.degree_eq_degree_of_associated hassoc]
    exact h q hq
  by_contra he
  exact (Polynomial.degree_pos_of_irreducible hg).not_le
    (Nat.WithBot.lt_one_iff_le_zero.mp (lt_of_le_of_ne hle he))

/-- The factor in the quotient field has an integer polynomial lift. -/
theorem nonsplit_reduction_exists_lifted_factor
    (I : Ideal ℤ) [I.IsMaximal] (P : Polynomial ℤ)
    (hn : ¬ (P.map (Ideal.Quotient.mk I)).Splits (RingHom.id (ℤ ⧸ I))) :
    ∃ Q : Polynomial ℤ,
      Q.map (Ideal.Quotient.mk I) ∈ normalizedFactors (P.map (Ideal.Quotient.mk I)) ∧
      1 < (Q.map (Ideal.Quotient.mk I)).degree := by
  obtain ⟨g, hg, hd⟩ := nonsplit_exists_higher_normalized_factor _ hn
  obtain ⟨Q, rfl⟩ := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective g
  exact ⟨Q, hg, hd⟩

/-- Outside the proved finite exception set, nonsplitting alone supplies
the actual local valuation obstruction. -/
theorem nonsplit_certificate_of_conductor_exceptions
    {K : Type*} [Field K] [NumberField K]
    (a : 𝓞 K) (T : Finset ℕ)
    (hT : ∀ p : ℕ, p.Prime → p ∉ T →
      (conductor ℤ a).comap (algebraMap ℤ (𝓞 K)) ⊔ Ideal.span {(p : ℤ)} = ⊤)
    (p : ℕ) (hp : p.Prime) (hgood : p ∉ T)
    (I : Ideal ℤ) [I.IsMaximal] (hI : I = Ideal.span {(p : ℤ)})
    (hn : ¬ ((minpoly ℤ a).map (Ideal.Quotient.mk I)).Splits (RingHom.id (ℤ ⧸ I))) :
    ∃ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      w.valuation K (p : K) < 1 ∧
      ∀ j : ℕ, w.valuation K ((a : K) - (j : K)) = 1 := by
  obtain ⟨Q, hQ, hd⟩ := nonsplit_reduction_exists_lifted_factor I _ hn
  exact factor_certificate_of_conductor_exceptions a T hT p hp hgood I hI Q hQ hd

end StrictEUnit
end
