import CharacterUnitLift
import PairingBaseChange
import EquivariantWeightChart
import ScalarExtendedRegular
import InvariantDescent
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Character lifting from an actual equivariant trivializing chart

This file assembles the checked tensor comparison, faithful descent, UFD
principality and regular representation. Existence of the indicated chart
and the character are inputs; no PV/E-function construction is asserted.
-/

open TensorProduct
open scoped TensorProduct
noncomputable section
namespace StrictEUnit

variable {B R T : Type*} [CommRing B] [IsDomain B] [UniqueFactorizationMonoid B]
  [CommRing R] [IsDomain R] [CommRing T] [Algebra B R] [Algebra B T]

/-- An actual weighted unit after a faithfully flat extension supplies the
previous local-pairing hypothesis. All tensor comparison maps are proved. -/
theorem exists_character_unit_of_local_weighted_unit
    (A : Type*) [CommRing A] [Algebra B A] [Module.FaithfullyFlat B A]
    (ρ ι : R →ₐ[B] T) (χ : Tˣ)
    (hinj : Function.Injective (algebraMap B R))
    (hfixed : ∀ r : R, ρ r = ι r → ∃ b : B, algebraMap B R b = r)
    (hinjA : Function.Injective (algebraMap A (A ⊗[B] R)))
    (hfixedA : ∀ r : A ⊗[B] R,
      weightBaseChangeAlgHom A ρ r = weightBaseChangeAlgHom A ι r →
      ∃ a : A, algebraMap A (A ⊗[B] R) a = r)
    (hunit : ∃ u : (A ⊗[B] R)ˣ,
      (u : A ⊗[B] R) ∈ weightSpace (weightBaseChangeAlgHom A ρ)
        (weightBaseChangeAlgHom A ι) ((1 : A) ⊗ₜ[B] (χ : T))) :
    ∃ v w : R, v ∈ weightSpace ρ ι (χ : T) ∧
      w ∈ weightSpace ρ ι (↑χ⁻¹ : T) ∧ v * w = 1 ∧ IsUnit v := by
  let ρA := weightBaseChangeAlgHom A ρ
  let ιA := weightBaseChangeAlgHom A ι
  let χA := extendedUnit (k := B) A χ
  let μ := scalarWeightPairing ρ ι χ hinj hfixed
  let ν := scalarWeightPairing ρA ιA χA hinjA hfixedA
  obtain ⟨u, hu⟩ := hunit
  let x : weightSpace ρA ιA (χA : A ⊗[B] T) := ⟨u, hu⟩
  let y : weightSpace ρA ιA (↑χA⁻¹ : A ⊗[B] T) :=
    ⟨↑u⁻¹, inverse_unit_opposite_weight ρA ιA χA u hu⟩
  have hone : ν (x ⊗ₜ[A] y) = 1 := by
    apply hinjA
    rw [scalarWeightPairing_tmul, map_one]
    exact Units.mul_inv u
  have hν : Function.Surjective ν := by
    intro a
    refine ⟨a • (x ⊗ₜ[A] y), ?_⟩
    rw [map_smul, hone, smul_eq_mul, mul_one]
  have hlocal : Function.Surjective (μ.lTensor A) :=
    lTensor_surjective_of_extended_weight_pairing A ρ ι (χ : T) (↑χ⁻¹ : T)
      hinjA μ (scalarWeightPairing_tmul ρ ι χ hinj hfixed)
      ν (scalarWeightPairing_tmul ρA ιA χA hinjA hfixedA) hν
  exact exists_character_unit_of_ufd_local_pairing ρ ι χ A hinj hfixed hlocal

/-- A faithfully flat equivariant chart to the ACTUAL scalar-extended regular
model yields a unit of the prescribed character. Invariant identification,
injectivity of the base map, and local-pairing surjectivity are all derived.
The hypotheses are geometric chart data, not these downstream conclusions. -/
theorem exists_character_unit_of_scalar_extended_regular_chart
    (k : Type*) [Field k] (H : Type*) [CommRing H] [Bialgebra k H]
    (A : Type*) [CommRing A] [Algebra B A] [Algebra k A]
    [Module.FaithfullyFlat B A]
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
  letI : Module.Flat k A := Module.Flat.of_free
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


#print axioms StrictEUnit.exists_character_unit_of_local_weighted_unit
#print axioms StrictEUnit.exists_character_unit_of_scalar_extended_regular_chart
