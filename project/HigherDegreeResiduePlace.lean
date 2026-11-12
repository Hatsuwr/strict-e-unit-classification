import NumberFieldPolynomialPrimeObstruction

noncomputable section
open scoped NumberField
namespace StrictEUnit

/-- A higher-degree irreducible equation over a field prevents its root
in any extension from lying in the base field. -/
theorem irreducible_residue_root_not_base
    {F E : Type*} [Field F] [CommRing E] [Nontrivial E] (f : F →+* E)
    (g : Polynomial F) (hg : Irreducible g) (hd : 1 < g.degree)
    (x : E) (hx : g.eval₂ f x = 0) : ∀ y : F, x ≠ f y := by
  intro y he
  rw [he, Polynomial.eval₂_at_apply] at hx
  have hz : g.eval y = 0 := f.injective (by simpa using hx)
  have hdeg := Polynomial.degree_eq_one_of_irreducible_of_root hg hz
  exact (ne_of_gt hd) hdeg

/-- A higher-degree residue equation at a specific prime ideal supplies
all local certificates, even if the original polynomial has roots at other places. -/
theorem numberField_higher_degree_residue_place
    {K : Type*} [Field K] [NumberField K]
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (p : ℕ) (hp : p.Prime) (hpw : (p : 𝓞 K) ∈ w.asIdeal)
    (a : 𝓞 K) (f : ZMod p →+* ((𝓞 K) ⧸ w.asIdeal))
    (g : Polynomial (ZMod p)) (hg : Irreducible g) (hd : 1 < g.degree)
    (hroot : g.eval₂ f (Ideal.Quotient.mk w.asIdeal a) = 0) :
    w.valuation K (p : K) < 1 ∧
      ∀ j : ℕ, w.valuation K ((a : K) - (j : K)) = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : CommRing (𝓞 K) := inferInstance
  letI : CommRing ((𝓞 K) ⧸ w.asIdeal) := inferInstance
  have hnot := irreducible_residue_root_not_base f g hg hd
    (Ideal.Quotient.mk w.asIdeal a) hroot
  constructor
  · have hlt := (w.valuation_lt_one_iff_dvd (K := K) (p : 𝓞 K)).mpr
      (Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (by simpa using hpw)))
    simpa using hlt
  · intro j
    have hnm : a - (j : 𝓞 K) ∉ w.asIdeal := by
      intro hm
      have he := (Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := w.asIdeal) a (j : 𝓞 K)).mpr hm
      apply hnot (j : ZMod p)
      simpa using he
    have hle := w.valuation_le_one (K := K) (a - (j : 𝓞 K))
    have hnlt : ¬ w.valuation K (algebraMap (𝓞 K) K (a - (j : 𝓞 K))) < 1 := by
      rw [w.valuation_lt_one_iff_dvd]
      intro hdiv
      exact hnm ((Ideal.dvd_iff_le.mp hdiv) (Ideal.subset_span (by simp)))
    have he := le_antisymm hle (le_of_not_gt hnlt)
    simpa using he

/-- The prime-field map in the actual residue ring is constructed from p membership. -/
def numberFieldResiduePrimeMap
    {K : Type*} [Field K] [NumberField K]
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (p : ℕ) (hp : p.Prime) (hpw : (p : 𝓞 K) ∈ w.asIdeal) :
    ZMod p →+* ((𝓞 K) ⧸ w.asIdeal) := by
  have hz : (p : (𝓞 K) ⧸ w.asIdeal) = 0 := by
    have h := (Ideal.Quotient.eq_zero_iff_mem).mpr hpw
    simpa only [map_natCast (Ideal.Quotient.mk w.asIdeal) p] using h
  letI : CharP ((𝓞 K) ⧸ w.asIdeal) p := (CharP.charP_iff_prime_eq_zero hp).mpr hz
  exact ZMod.castHom (dvd_refl p) _

/-- Concrete higher-degree residue data at an actual prime ideal suffices;
the prime-field embedding and valuation are no longer separate inputs. -/
theorem numberField_higher_degree_residue_certificate
    {K : Type*} [Field K] [NumberField K]
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (p : ℕ) (hp : p.Prime) (hpw : (p : 𝓞 K) ∈ w.asIdeal)
    (a : 𝓞 K) (g : Polynomial (ZMod p)) (hg : Irreducible g) (hd : 1 < g.degree)
    (hroot : g.eval₂ (numberFieldResiduePrimeMap w p hp hpw)
      (Ideal.Quotient.mk w.asIdeal a) = 0) :
    w.valuation K (p : K) < 1 ∧
      ∀ j : ℕ, w.valuation K ((a : K) - (j : K)) = 1 :=
  numberField_higher_degree_residue_place w p hp hpw a
    (numberFieldResiduePrimeMap w p hp hpw) g hg hd hroot

end StrictEUnit
end
