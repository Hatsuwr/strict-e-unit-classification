import GaloisNonsplitPlaceCertificates
import GaloisNonsplitFiniteExceptions
import CertifiedPrimeSummability

noncomputable section
open scoped NumberField
open IntermediateField
namespace StrictEUnit

/-- Binomial-prefix arithmetic of an integral primitive element rules out
any nontrivial finite Galois extension. Prime supply and places are derived. -/
theorem binomial_galois_powerBasis_degree_one
    {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
    (a : 𝓞 K) (B : PowerBasis ℚ K) (hgen : B.gen = (a : K))
    (ha : BinomialPrefixDenominators (a : K)) : Module.finrank ℚ K = 1 := by
  classical
  by_contra hne
  have hd : 1 < Module.finrank ℚ K := by
    have := Module.finrank_pos (R := ℚ) (M := K)
    omega
  obtain ⟨T,hT⟩ := galois_nonsplit_powerBasis_place_certificates a B hgen
  let P : Set ℕ := {p | p.Prime ∧ ¬GaloisCompletelySplitAt K p ∧ p ∉ T}
  have hw : ∀ p : P, ∃ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      w.valuation K (p.val : K) < 1 ∧
      ∀ j : ℕ, w.valuation K ((a : K) - (j : K)) = 1 :=
    fun p => hT p p.property.1 p.property.2.2 p.property.2.1
  choose w hwv hwu using hw
  let v := fun p : ℕ => if h : p ∈ P then (w ⟨p,h⟩).valuation K else (numberField_exists_prime_place K 2 Nat.prime_two).choose
  have hsum := binomialPrefixDenominators_certified_prime_summable (a : K) ha P v
    (fun p hp => hp.1)
    (fun p hp => by simpa [v, hp] using hwv ⟨p,hp⟩)
    (fun p hp r _ => by simpa [v, hp] using hwu ⟨p,hp⟩ r)
  apply galois_nonsplit_log_weight_not_summable_outside_finite K hd T
  apply hsum.congr
  intro p
  by_cases h : p.Prime ∧ ¬GaloisCompletelySplitAt K p ∧ p ∉ T <;> simp [P, h]

/-- Instantiates the power basis from the actual primitive generator,
not an independently chosen generator. -/
theorem binomial_galois_integral_primitive_degree_one
    {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
    (a : K) (hgen : ℚ⟮a⟯ = ⊤) (hi : IsIntegral ℤ a)
    (ha : BinomialPrefixDenominators a) : Module.finrank ℚ K = 1 := by
  let B := (IntermediateField.adjoin.powerBasis (IsIntegral.of_finite ℚ a)).map
    ((IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv)
  apply binomial_galois_powerBasis_degree_one (⟨a,hi⟩ : 𝓞 K) B _ ha
  rfl

end StrictEUnit
end
