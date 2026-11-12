import TorsorUnitLift

/-! Generalization from a field coefficient ring to a commutative ring,
with the exact required flatness hypothesis supplied explicitly. -/
open TensorProduct
open scoped TensorProduct
noncomputable section
namespace StrictEUnit
variable {B R T : Type*} [CommRing B] [IsDomain B] [UniqueFactorizationMonoid B]
  [CommRing R] [IsDomain R] [CommRing T] [Algebra B R] [Algebra B T]

/-- A faithfully flat equivariant chart to the ACTUAL scalar-extended regular
model yields a unit of the prescribed character. Invariant identification,
injectivity of the base map, and local-pairing surjectivity are all derived.
The hypotheses are geometric chart data, not these downstream conclusions. -/
theorem exists_character_unit_of_flat_regular_chart
    (k : Type*) [CommRing k] (H : Type*) [CommRing H] [Bialgebra k H]
    (A : Type*) [CommRing A] [Algebra B A] [Algebra k A]
    [Module.FaithfullyFlat B A] [Module.Flat k A]
    (ρ ι : R →ₐ[B] T) (χ : Tˣ) (u : Hˣ)
    (hu : Coalgebra.comul (R := k) (u : H) = (u : H) ⊗ₜ[k] (u : H))
    (e : A ⊗[B] R ≃ₐ[A] A ⊗[k] H)
    (E : A ⊗[B] T ≃ₐ[A] A ⊗[k] (H ⊗[k] H))
    (hρ : ∀ r, E (weightBaseChangeAlgHom A ρ r) =
      weightBaseChangeAlgHom A (Bialgebra.comulAlgHom k H) (e r))
    (hι : ∀ r, E (weightBaseChangeAlgHom A ι r) =
      weightBaseChangeAlgHom A
        (Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] H) (e r))
    (hχ : E ((1 : A) ⊗ₜ[B] (χ : T)) =
      (1 : A) ⊗ₜ[k] ((1 : H) ⊗ₜ[k] (u : H))) :
    ∃ v w : R, v ∈ weightSpace ρ ι (χ : T) ∧
      w ∈ weightSpace ρ ι (↑χ⁻¹ : T) ∧ v * w = 1 ∧ IsUnit v := by
  have hinjA : Function.Injective (algebraMap A (A ⊗[B] R)) :=
    chart_base_injective e (extended_regular_base_injective (H := H) A)
  have hfixedA : ∀ r : A ⊗[B] R,
      weightBaseChangeAlgHom A ρ r = weightBaseChangeAlgHom A ι r →
      ∃ a : A, algebraMap A (A ⊗[B] R) a = r :=
    chart_invariants_are_scalars e E _ _ _ _ hρ hι
      (extended_regular_invariants_are_scalars (H := H) A)
  have hinj := scalar_inclusion_injective_descends A ρ ι hinjA
  have hfixed := invariant_image_descends A ρ ι hfixedA
  have hunit : ∃ v : (A ⊗[B] R)ˣ,
      (v : A ⊗[B] R) ∈ weightSpace (weightBaseChangeAlgHom A ρ)
        (weightBaseChangeAlgHom A ι) ((1 : A) ⊗ₜ[B] (χ : T)) := by
    apply chart_weighted_unit e E _ _ _ _ hρ hι
      ((1 : A) ⊗ₜ[B] (χ : T)) (extendedUnit (k := k) A u)
    rw [hχ]
    exact extended_regular_unit_weight A u hu
  exact exists_character_unit_of_local_weighted_unit A ρ ι χ
    hinj hfixed hinjA hfixedA hunit

end StrictEUnit
#print axioms StrictEUnit.exists_character_unit_of_flat_regular_chart
