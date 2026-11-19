import KummerSplitPrimeCount

noncomputable section
attribute [local instance] Classical.propDecidable Ideal.Quotient.field
open scoped NumberField
namespace StrictEUnit

/-- Outside an actual finite union of conductor and repeated-root exceptions,
every failure of complete splitting supplies the required valuation place.
The generator and its power basis are the same ones throughout. -/
theorem galois_nonsplit_powerBasis_place_certificates
    {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
    (a : 𝓞 K) (B : PowerBasis ℚ K) (hgen : B.gen = (a : K)) :
    ∃ T : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ T →
      ¬ GaloisCompletelySplitAt K p →
      ∃ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        w.valuation K (p : K) < 1 ∧
        ∀ j : ℕ, w.valuation K ((a : K) - (j : K)) = 1 := by
  obtain ⟨Tc,hTc⟩ := numberField_powerBasis_conductor_finite_exceptions a B hgen
  obtain ⟨Ts,hTs⟩ := integral_minpoly_quotient_separable_finite_exceptions a
  refine ⟨Tc ∪ Ts, ?_⟩
  intro p hp hgood hns
  have hpc : p ∉ Tc := fun h => hgood (Finset.mem_union_left _ h)
  have hps : p ∉ Ts := fun h => hgood (Finset.mem_union_right _ h)
  let q : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hq0 : q ≠ ⊥ := by simpa [q, Ideal.span_singleton_eq_bot] using hp.ne_zero
  letI : q.IsPrime := (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp hp)
  letI : q.IsMaximal := (inferInstance : q.IsPrime).isMaximal hq0
  apply nonsplit_certificate_of_conductor_exceptions a Tc hTc p hp hpc q rfl
  intro hsp
  exact hns (powerBasis_split_separable_completely_split a B hgen p hp
    (hTc p hp hpc) (hTs p hp hps) hsp)

end StrictEUnit
end
