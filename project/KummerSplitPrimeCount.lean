import SplitSeparableFactorCount
import PrimeComplementConstraint

noncomputable section
attribute [local instance] Classical.propDecidable Ideal.Quotient.field
open Polynomial UniqueFactorizationMonoid
open scoped NumberField
namespace StrictEUnit

/-- Kummer--Dedekind turns a split separable reduction into an exact count
of primes over the underlying rational prime, outside the conductor. -/
theorem kummer_split_separable_prime_count
    {K : Type*} [Field K] [NumberField K]
    (a : 𝓞 K) (I : Ideal ℤ) [hI : I.IsMaximal] (hI0 : I ≠ ⊥)
    (hc : (conductor ℤ a).comap (algebraMap ℤ (𝓞 K)) ⊔ I = ⊤)
    (hs : ((minpoly ℤ a).map (Ideal.Quotient.mk I)).Separable)
    (hsp : ((minpoly ℤ a).map (Ideal.Quotient.mk I)).Splits (RingHom.id _)) :
    (Ideal.primesOver I (𝓞 K)).ncard = (minpoly ℤ a).natDegree := by
  let e := KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
    hI hI0 hc (NumberField.RingOfIntegers.isIntegral a)
  have hset : ∀ J : Ideal (𝓞 K),
      J ∈ normalizedFactors (I.map (algebraMap ℤ (𝓞 K))) ↔
        J ∈ Ideal.primesOver I (𝓞 K) := by
    intro J
    rw [← coe_primesOverFinset hI0 (𝓞 K)]
    simp only [primesOverFinset, factors_eq_normalizedFactors, Finset.mem_coe,
      Multiset.mem_toFinset]
  let e' := Equiv.subtypeEquivRight hset
  have hm := (minpoly.monic (NumberField.RingOfIntegers.isIntegral a)).map (Ideal.Quotient.mk I)
  calc
    _ = Nat.card {J : Ideal (𝓞 K) // J ∈ normalizedFactors (I.map (algebraMap ℤ (𝓞 K)))} := by
      rw [← Set.Nat.card_coe_set_eq]; exact (Nat.card_congr e').symm
    _ = _ := Nat.card_congr e
    _ = _ := split_separable_normalized_factor_count _ hm hs hsp
    _ = _ := (minpoly.monic (NumberField.RingOfIntegers.isIntegral a)).natDegree_map _

/-- The Galois fundamental identity forces complete splitting once the
actual prime count is the full extension degree. -/
theorem galois_completely_split_of_full_prime_count
    (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    (p : ℕ) (hp : p.Prime)
    (hc : (Ideal.primesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 K)).ncard =
      Module.finrank ℚ K) : GaloisCompletelySplitAt K p := by
  let q : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hq0 : q ≠ ⊥ := by simpa [q, Ideal.span_singleton_eq_bot] using hp.ne_zero
  letI : q.IsPrime := (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp hp)
  letI : q.IsMaximal := (inferInstance : q.IsPrime).isMaximal hq0
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hq0 (𝓞 K) ℚ K
  change (Ideal.primesOver q (𝓞 K)).ncard * (_ * _) = _ at h
  rw [hc] at h
  have hd := Module.finrank_pos (R := ℚ) (M := K)
  have heq : Ideal.ramificationIdxIn q (𝓞 K) * Ideal.inertiaDegIn q (𝓞 K) = 1 :=
    (Nat.mul_left_cancel hd (show Module.finrank ℚ K * _ = Module.finrank ℚ K * 1 by simpa using h))
  exact (mul_eq_one.mp heq)

/-- The actual integral power-basis generator identifies polynomial degree
with the extension degree; split separable reduction then implies e=f=1. -/
theorem powerBasis_split_separable_completely_split
    {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
    (a : 𝓞 K) (B : PowerBasis ℚ K) (hgen : B.gen = (a : K))
    (p : ℕ) (hp : p.Prime)
    [hI : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsMaximal]
    (hc : (conductor ℤ a).comap (algebraMap ℤ (𝓞 K)) ⊔ Ideal.span {(p : ℤ)} = ⊤)
    (hs : ((minpoly ℤ a).map (Ideal.Quotient.mk (Ideal.span {(p : ℤ)}))).Separable)
    (hsp : ((minpoly ℤ a).map (Ideal.Quotient.mk (Ideal.span {(p : ℤ)}))).Splits
      (RingHom.id _)) : GaloisCompletelySplitAt K p := by
  apply galois_completely_split_of_full_prime_count K p hp
  have hI0 : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero
  rw [kummer_split_separable_prime_count a _ hI0 hc hs hsp]
  have hmin := minpoly.isIntegrallyClosed_eq_field_fractions ℚ K
    (NumberField.RingOfIntegers.isIntegral a)
  have hd := congrArg Polynomial.natDegree hmin
  rw [(minpoly.monic (NumberField.RingOfIntegers.isIntegral a)).natDegree_map] at hd
  rw [← hd]
  change (minpoly ℚ (a : K)).natDegree = _
  rw [← hgen, B.natDegree_minpoly, B.finrank]

/-- Finite repeated-root exceptions in the literal integer quotient ring. -/
theorem integral_minpoly_quotient_separable_finite_exceptions
    {K : Type*} [Field K] [NumberField K] (a : 𝓞 K) :
    ∃ T : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ T →
      ((minpoly ℤ a).map (Ideal.Quotient.mk (Ideal.span {(p : ℤ)}))).Separable := by
  obtain ⟨T,hT⟩ := integral_minpoly_separable_reduction_finite_exceptions a
  refine ⟨T, ?_⟩
  intro p hp hgood
  have h := (hT p hp hgood).map (f := (Int.quotientSpanNatEquivZMod p).symm.toRingHom)
  rw [Polynomial.map_map] at h
  have he : (Int.quotientSpanNatEquivZMod p).symm.toRingHom.comp
      (Int.castRingHom (ZMod p)) = Ideal.Quotient.mk (Ideal.span {(p : ℤ)}) := by
    ext x
    simp
  rwa [he] at h

end StrictEUnit
end
