import CanonicalTorsorUnitLift

/-! Canonical-torsor invariants, with no global invariant-image premise. -/
open scoped TensorProduct
noncomputable section
namespace StrictEUnit
variable {B R H : Type*} [CommRing B] [CommRing R] [Algebra B R]
  [CommRing H] [Bialgebra B H] [Module.FaithfullyFlat B R]

/-- Faithful flatness and the actual canonical torsor chart prove that every
invariant lies in the base. Domain and UFD hypotheses are unnecessary here. -/
theorem canonical_torsor_invariants_are_scalars
    (ρ : R →ₐ[B] R ⊗[B] H)
    (hcan : Function.Bijective (torsorCanonical ρ))
    (hcoassoc : ∀ s : R,
      Algebra.TensorProduct.assoc B R H H
        (Algebra.TensorProduct.map ρ (AlgHom.id B H) (ρ s)) =
      weightBaseChangeAlgHom R (Bialgebra.comulAlgHom B H) (ρ s)) :
    ∀ r : R, ρ r = (Algebra.TensorProduct.includeLeft : R →ₐ[B] R ⊗[B] H) r →
      ∃ b : B, algebraMap B R b = r := by
  let e := torsorCanonicalEquiv ρ hcan
  apply invariant_image_descends R ρ Algebra.TensorProduct.includeLeft
  exact chart_invariants_are_scalars e (torsorTargetChart e) _ _ _ _
    (torsorCanonicalEquiv_coaction ρ hcan hcoassoc)
    (torsorTargetChart_includeLeft e)
    (extended_regular_invariants_are_scalars (H := H) R)
end StrictEUnit
#print axioms StrictEUnit.canonical_torsor_invariants_are_scalars
