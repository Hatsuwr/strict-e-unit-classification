import PerfectPairingCyclic
import PairingUnitLift
import WeightSpaces

/-!
# A regular unit from a locally surjective character pairing over a UFD

This closes the global-generator/Picard step for actual submodules of a
domain. The generator, fractional-ideal realization, and inverse are all
constructed in the preceding checked proofs, not assumed here.

For the manuscript one still must instantiate the actual rings and coaction,
prove the invariant-ring condition, and connect a torsor trivialization to
the stated local surjectivity condition. No strict E-function theorem is
claimed by this general algebra result.
-/

open TensorProduct

namespace StrictEUnit

variable {B R : Type*} [CommRing B] [IsDomain B] [UniqueFactorizationMonoid B]
    [CommRing R] [IsDomain R] [Algebra B R]

/-- No generator or freeness hypothesis: faithful flatness descends the
pairing, UFD arithmetic constructs a generator, and the pairing supplies
its regular inverse in the prescribed opposite submodule. -/
theorem exists_regular_inverse_of_ufd_local_pairing
    (A : Type*) [AddCommGroup A] [Module B A] [Module.FaithfullyFlat B A]
    (hinj : Function.Injective (algebraMap B R))
    (M N : Submodule B R) (μ : M ⊗[B] N →ₗ[B] B)
    (hproduct : ∀ (m : M) (n : N),
      algebraMap B R (μ (m ⊗ₜ[B] n)) = (m : R) * (n : R))
    (hlocal : Function.Surjective (μ.lTensor A)) :
    ∃ v : M, (∀ m : M, ∃ b : B, m = b • v) ∧
      ∃ w : N, (v : R) * (w : R) = 1 := by
  have hμ : Function.Surjective μ := pairing_surjective_of_faithfully_flat A μ hlocal
  obtain ⟨v, hv⟩ := cyclic_of_surjective_multiplication_pairing hinj M N μ hμ hproduct
  exact ⟨v, hv, regular_inverse_of_faithfully_flat_pairing A M N μ hproduct v hv hlocal⟩

/-- The concrete weight equalizer contains an actual unit, with inverse of
the opposite weight. UFD principality and a generator are derived, not
inserted as assumed Picard or rank-one hypotheses. -/
theorem exists_character_unit_of_ufd_local_pairing
    {T : Type*} [CommRing T] [Algebra B T]
    (ρ ι : R →ₐ[B] T) (χ : Tˣ)
    (A : Type*) [AddCommGroup A] [Module B A] [Module.FaithfullyFlat B A]
    (hinj : Function.Injective (algebraMap B R))
    (hfixed : ∀ r : R, ρ r = ι r → ∃ b : B, algebraMap B R b = r)
    (hlocal : Function.Surjective ((scalarWeightPairing ρ ι χ hinj hfixed).lTensor A)) :
    ∃ v w : R, v ∈ weightSpace ρ ι (χ : T) ∧
      w ∈ weightSpace ρ ι (↑χ⁻¹ : T) ∧ v * w = 1 ∧ IsUnit v := by
  obtain ⟨v, _, w, hw⟩ := exists_regular_inverse_of_ufd_local_pairing A hinj
    (weightSpace ρ ι (χ : T)) (weightSpace ρ ι (↑χ⁻¹ : T))
    (scalarWeightPairing ρ ι χ hinj hfixed)
    (scalarWeightPairing_tmul ρ ι χ hinj hfixed) hlocal
  exact ⟨v, w, v.property, w.property, hw, isUnit_of_mul_eq_one (v : R) (w : R) hw⟩

end StrictEUnit

#print axioms StrictEUnit.exists_regular_inverse_of_ufd_local_pairing
#print axioms StrictEUnit.exists_character_unit_of_ufd_local_pairing
