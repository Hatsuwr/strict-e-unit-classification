import KummerPrimeSelection

noncomputable section
attribute [local instance] Ideal.Quotient.field
attribute [local instance] Classical.propDecidable
open scoped NumberField
open UniqueFactorizationMonoid
namespace StrictEUnit

/-- The selected Kummer prime provides the local certificate directly from
a higher-degree factor. The conductor hypothesis is retained explicitly. -/
theorem numberField_kummer_higher_degree_certificate
    {K : Type*} [Field K] [NumberField K]
    (a : 𝓞 K) (I : Ideal ℤ) [hI : I.IsMaximal] (hI0 : I ≠ ⊥)
    (hc : (conductor ℤ a).comap (algebraMap ℤ (𝓞 K)) ⊔ I = ⊤)
    (Q : Polynomial ℤ)
    (hQ : Q.map (Ideal.Quotient.mk I) ∈ normalizedFactors
      ((minpoly ℤ a).map (Ideal.Quotient.mk I)))
    (hd : 1 < (Q.map (Ideal.Quotient.mk I)).degree)
    (p : ℕ) (hpI : (p : ℤ) ∈ I) :
    ∃ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      w.valuation K (p : K) < 1 ∧
      ∀ j : ℕ, w.valuation K ((a : K) - (j : K)) = 1 := by
  classical
  letI : CommRing (𝓞 K) := inferInstance
  obtain ⟨w, _, hIw, hQa⟩ := numberField_kummer_prime_from_factor a I hI0 hc Q hQ
  letI : CommRing ((𝓞 K) ⧸ w.asIdeal) := inferInstance
  let f : (ℤ ⧸ I) →+* ((𝓞 K) ⧸ w.asIdeal) :=
    Ideal.Quotient.lift I ((Ideal.Quotient.mk w.asIdeal).comp (algebraMap ℤ (𝓞 K)))
      (fun z hz => Ideal.Quotient.eq_zero_iff_mem.mpr
        (hIw (Ideal.mem_map_of_mem _ hz)))
  have hf : f.comp (Ideal.Quotient.mk I) =
      (Ideal.Quotient.mk w.asIdeal).comp (algebraMap ℤ (𝓞 K)) := by
    ext z
    rfl
  have hroot : (Q.map (Ideal.Quotient.mk I)).eval₂ f
      (Ideal.Quotient.mk w.asIdeal a) = 0 := by
    rw [Polynomial.eval₂_map, hf]
    rw [← Polynomial.hom_eval₂]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hQa
  have hnot := irreducible_residue_root_not_base f _
    (irreducible_of_normalized_factor _ hQ) hd _ hroot
  refine ⟨w, ?_, ?_⟩
  · have hpw : (p : 𝓞 K) ∈ w.asIdeal := by
      simpa using hIw (Ideal.mem_map_of_mem (algebraMap ℤ (𝓞 K)) hpI)
    have hlt := (w.valuation_lt_one_iff_dvd (K := K) (p : 𝓞 K)).mpr
      (Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (by simpa using hpw)))
    simpa using hlt
  · intro j
    have hnm : a - (j : 𝓞 K) ∉ w.asIdeal := by
      intro hm
      have he := (Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := w.asIdeal) a (j : 𝓞 K)).mpr hm
      apply hnot (j : ℤ ⧸ I)
      simpa using he
    have hle := w.valuation_le_one (K := K) (a - (j : 𝓞 K))
    have hnlt : ¬ w.valuation K (algebraMap (𝓞 K) K (a - (j : 𝓞 K))) < 1 := by
      rw [w.valuation_lt_one_iff_dvd]
      intro hdiv
      exact hnm ((Ideal.dvd_iff_le.mp hdiv) (Ideal.subset_span (by simp)))
    simpa using le_antisymm hle (le_of_not_gt hnlt)

end StrictEUnit
end
