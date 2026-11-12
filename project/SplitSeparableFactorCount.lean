import SeparableReductionExceptions
import NonsplitFactorSelection
import SplitPrimeNormCertificates

noncomputable section
attribute [local instance] Classical.propDecidable
open Polynomial UniqueFactorizationMonoid
namespace StrictEUnit

/-- A split separable monic polynomial has exactly degree-many distinct
normalized factors. Multiplicities are not silently discarded. -/
theorem split_separable_normalized_factor_count
    {F : Type*} [Field F] (P : F[X]) (hm : P.Monic)
    (hs : P.Separable) (hsp : P.Splits (RingHom.id F)) :
    Nat.card {g : F[X] // g ∈ normalizedFactors P} = P.natDegree := by
  classical
  have hn := (squarefree_iff_nodup_normalizedFactors hm.ne_zero).mp hs.squarefree
  have hg : ∀ g ∈ normalizedFactors P, g.natDegree = 1 := by
    intro g hg
    have hi := irreducible_of_normalized_factor _ hg
    have hd := (Polynomial.splits_iff _ _ |>.mp hsp).resolve_left hm.ne_zero hi
      (by simpa only [map_id] using dvd_of_mem_normalizedFactors hg)
    exact natDegree_eq_of_degree_eq_some hd
  have hprod : (normalizedFactors P).prod = P := by
    simpa [hm.leadingCoeff] using leadingCoeff_mul_prod_normalizedFactors P
  have hdegree := natDegree_multiset_prod_of_monic
    (t := normalizedFactors P) (fun g hg => by
      rw [← normalize_normalized_factor g hg]
      exact monic_normalize (irreducible_of_normalized_factor g hg).ne_zero)
  rw [hprod] at hdegree
  have hmap : (normalizedFactors P).map natDegree = (normalizedFactors P).map (fun _ => 1) :=
    Multiset.map_congr rfl hg
  rw [hmap] at hdegree
  have he : {g : F[X] // g ∈ normalizedFactors P} ≃
      {g : F[X] // g ∈ (normalizedFactors P).toFinset} :=
    Equiv.subtypeEquivRight (fun _ => Multiset.mem_toFinset.symm)
  rw [Nat.card_congr he, Nat.card_eq_fintype_card, Fintype.card_coe,
    Multiset.toFinset_card_of_nodup hn]
  simpa using hdegree.symm

end StrictEUnit
end
