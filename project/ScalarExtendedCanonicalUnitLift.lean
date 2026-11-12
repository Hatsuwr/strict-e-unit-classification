import CanonicalTorsorUnitLift
import BialgebraBaseChangeLaws

/-!
# A constant-field character on a canonical torsor over the base

The group algebra over B is constructed as B ⊗[k] H, with its actual
scalar-extended bialgebra structure. Neither a bialgebra structure on B nor
an assumed bialgebra structure on the tensor extension is needed.
The actual PV coaction and canonical torsor criterion remain inputs.
-/
open TensorProduct
open scoped TensorProduct
noncomputable section
namespace StrictEUnit

/-- The canonical torsor theorem with the group algebra and character
actually extended from the coefficient ring. No chart or scalar-extension
bialgebra premise is supplied in place of its construction. -/
theorem exists_character_unit_of_scalar_extended_canonical_torsor
    {k B R H : Type*} [CommRing k] [CommRing B] [Algebra k B]
    [IsDomain B] [UniqueFactorizationMonoid B]
    [CommRing R] [IsDomain R] [Algebra B R] [Module.FaithfullyFlat B R]
    [CommRing H] [Bialgebra k H]
    (ρ : R →ₐ[B] R ⊗[B] (B ⊗[k] H))
    (hcan : Function.Bijective (torsorCanonical ρ))
    (hcoassoc : ∀ s : R,
      Algebra.TensorProduct.assoc B R (B ⊗[k] H) (B ⊗[k] H)
        (Algebra.TensorProduct.map ρ (AlgHom.id B (B ⊗[k] H)) (ρ s)) =
      weightBaseChangeAlgHom R (baseChangeComul (k := k) (H := H) B) (ρ s))
    (χ : Hˣ)
    (hχ : Coalgebra.comul (R := k) (χ : H) = (χ : H) ⊗ₜ[k] (χ : H)) :
    ∃ v w : R,
      ρ v = v ⊗ₜ[B] ((1 : B) ⊗ₜ[k] (χ : H)) ∧
      ρ w = w ⊗ₜ[B] ((1 : B) ⊗ₜ[k] (↑χ⁻¹ : H)) ∧
      v * w = 1 ∧ IsUnit v := by
  letI := baseChangeBialgebra (k := k) (H := H) B
  let u := Units.map
    (Algebra.TensorProduct.includeRight : H →ₐ[k] B ⊗[k] H).toMonoidHom χ
  exact exists_character_unit_of_canonical_torsor ρ hcan hcoassoc u
    (baseChange_grouplike_unit B χ hχ)

end StrictEUnit
#print axioms StrictEUnit.exists_character_unit_of_scalar_extended_canonical_torsor
