import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.Algebra.Algebra.Bilinear

/-!
# Weight modules, base change, and their actual multiplication pairing

The two algebra maps below model the coaction and the inclusion into its
codomain. No torsor is postulated or constructed. The definition is the real
equalizer of those maps, not a new name for a desired conclusion.

We prove flat preservation of this equalizer, multiplication of weights,
the inverse-character pairing, and comparison of same-weight units under an
explicit invariant-ring hypothesis. The torsor, Picard, and local
trivialization theorems needed to supply those hypotheses remain separate.
-/

open scoped TensorProduct
open TensorProduct

noncomputable section

namespace StrictEUnit

section Weights

variable {B R T : Type*} [CommRing B] [CommRing R] [CommRing T]
    [Algebra B R] [Algebra B T]

/-- Elements transforming with a fixed multiplier in the coaction codomain. -/
def weightSpace (ρ ι : R →ₐ[B] T) (χ : T) : Submodule B R :=
  LinearMap.eqLocus ρ.toLinearMap ((LinearMap.mulRight B χ).comp ι.toLinearMap)

@[simp] theorem mem_weightSpace (ρ ι : R →ₐ[B] T) (χ : T) (r : R) :
    r ∈ weightSpace ρ ι χ ↔ ρ r = ι r * χ := Iff.rfl

/-- Multiplicativity is proved for actual ring elements, not assumed as a
property of the weight modules. -/
theorem weightSpace_mul (ρ ι : R →ₐ[B] T) {χ ψ : T} {x y : R}
    (hx : x ∈ weightSpace ρ ι χ) (hy : y ∈ weightSpace ρ ι ψ) :
    x * y ∈ weightSpace ρ ι (χ * ψ) := by
  change ρ (x * y) = ι (x * y) * (χ * ψ)
  rw [map_mul, map_mul, (mem_weightSpace ρ ι χ x).mp hx,
    (mem_weightSpace ρ ι ψ y).mp hy]
  ac_rfl

/-- Flat base change preserves the actual weight equalizer. The right side
uses the tensor extensions of the two defining linear maps; no comparison
with a geometric torsor chart is asserted here. -/
noncomputable def weightSpaceBaseChangeEquiv (ρ ι : R →ₐ[B] T) (χ : T)
    (A : Type*) [CommRing A] [Algebra B A] [Module.Flat B A] :
    A ⊗[B] (weightSpace ρ ι χ) ≃ₗ[A]
      LinearMap.eqLocus (AlgebraTensorModule.lTensor A A ρ.toLinearMap)
        (AlgebraTensorModule.lTensor A A
          ((LinearMap.mulRight B χ).comp ι.toLinearMap)) :=
  LinearMap.tensorEqLocusEquiv A A ρ.toLinearMap
    ((LinearMap.mulRight B χ).comp ι.toLinearMap)

/-- The equalizer isomorphism is the canonical map on pure tensors. -/
theorem weightSpaceBaseChangeEquiv_tmul (ρ ι : R →ₐ[B] T) (χ : T)
    (A : Type*) [CommRing A] [Algebra B A] [Module.Flat B A]
    (a : A) (x : weightSpace ρ ι χ) :
    ((weightSpaceBaseChangeEquiv ρ ι χ A) (a ⊗ₜ[B] x) : A ⊗[B] R) =
      a ⊗ₜ[B] (x : R) := rfl

/-- Inverse weights multiply into the invariant submodule. -/
theorem opposite_weight_mul_fixed (ρ ι : R →ₐ[B] T) (χ : Tˣ)
    (x : weightSpace ρ ι (χ : T)) (y : weightSpace ρ ι (↑χ⁻¹ : T)) :
    (x : R) * (y : R) ∈ weightSpace ρ ι 1 := by
  simpa only [Units.mul_inv] using
    weightSpace_mul ρ ι x.property y.property

/-- The actual multiplication bilinear map for opposite weight modules. -/
def oppositeWeightMulBilinear (ρ ι : R →ₐ[B] T) (χ : Tˣ) :
    weightSpace ρ ι (χ : T) →ₗ[B]
      weightSpace ρ ι (↑χ⁻¹ : T) →ₗ[B] weightSpace ρ ι 1 where
  toFun x :=
    { toFun := fun y => ⟨(x : R) * (y : R), opposite_weight_mul_fixed ρ ι χ x y⟩
      map_add' := by intro y z; ext; exact mul_add _ _ _
      map_smul' := by intro b y; ext; exact mul_smul_comm _ _ _ }
  map_add' := by intro x y; ext z; exact add_mul _ _ _
  map_smul' := by intro b x; ext y; exact smul_mul_assoc _ _ _

/-- The inverse-character tensor pairing has its multiplication, codomain,
and bilinearity constructed rather than supplied as hypotheses. -/
def oppositeWeightPairing (ρ ι : R →ₐ[B] T) (χ : Tˣ) :
    (weightSpace ρ ι (χ : T)) ⊗[B] (weightSpace ρ ι (↑χ⁻¹ : T)) →ₗ[B]
      weightSpace ρ ι 1 :=
  TensorProduct.lift (oppositeWeightMulBilinear ρ ι χ)

@[simp] theorem oppositeWeightPairing_tmul (ρ ι : R →ₐ[B] T) (χ : Tˣ)
    (x : weightSpace ρ ι (χ : T)) (y : weightSpace ρ ι (↑χ⁻¹ : T)) :
    (oppositeWeightPairing ρ ι χ (x ⊗ₜ[B] y) : R) = (x : R) * (y : R) := rfl

/-- Base scalars are invariant because both maps are B-algebra maps. -/
def scalarsToFixed (ρ ι : R →ₐ[B] T) : B →ₗ[B] weightSpace ρ ι 1 :=
  (Algebra.linearMap B R).codRestrict (weightSpace ρ ι 1) (by
    intro b
    change ρ (algebraMap B R b) = ι (algebraMap B R b) * 1
    simp)

@[simp] theorem scalarsToFixed_coe (ρ ι : R →ₐ[B] T) (b : B) :
    (scalarsToFixed ρ ι b : R) = algebraMap B R b := rfl

/-- Identification of invariants with the base ring. Only injectivity of
the base map and the stated invariant-image condition are assumed. In a
torsor application these conditions must be proved separately. -/
noncomputable def scalarsFixedEquiv (ρ ι : R →ₐ[B] T)
    (hinj : Function.Injective (algebraMap B R))
    (hfixed : ∀ r : R, ρ r = ι r → ∃ b : B, algebraMap B R b = r) :
    B ≃ₗ[B] weightSpace ρ ι 1 :=
  LinearEquiv.ofBijective (scalarsToFixed ρ ι) ⟨by
    intro x y h
    exact hinj (congrArg Subtype.val h), by
    intro x
    obtain ⟨b, hb⟩ := hfixed x (by
      simpa only [mem_weightSpace, mul_one] using x.property)
    exact ⟨b, Subtype.ext hb⟩⟩

/-- The scalar-valued tensor pairing constructed from actual multiplication
and the invariant-ring identification. No local isomorphism is assumed here. -/
noncomputable def scalarWeightPairing (ρ ι : R →ₐ[B] T) (χ : Tˣ)
    (hinj : Function.Injective (algebraMap B R))
    (hfixed : ∀ r : R, ρ r = ι r → ∃ b : B, algebraMap B R b = r) :
    (weightSpace ρ ι (χ : T)) ⊗[B] (weightSpace ρ ι (↑χ⁻¹ : T)) →ₗ[B] B :=
  (scalarsFixedEquiv ρ ι hinj hfixed).symm.toLinearMap.comp
    (oppositeWeightPairing ρ ι χ)

/-- Pure tensors evaluate to their actual product in the ambient algebra. -/
theorem scalarWeightPairing_tmul (ρ ι : R →ₐ[B] T) (χ : Tˣ)
    (hinj : Function.Injective (algebraMap B R))
    (hfixed : ∀ r : R, ρ r = ι r → ∃ b : B, algebraMap B R b = r)
    (x : weightSpace ρ ι (χ : T)) (y : weightSpace ρ ι (↑χ⁻¹ : T)) :
    algebraMap B R (scalarWeightPairing ρ ι χ hinj hfixed (x ⊗ₜ[B] y)) =
      (x : R) * (y : R) := by
  have h := (scalarsFixedEquiv ρ ι hinj hfixed).apply_symm_apply
    (oppositeWeightPairing ρ ι χ (x ⊗ₜ[B] y))
  exact congrArg Subtype.val h

/-- The inverse of a genuine weighted unit has the inverse weight. -/
theorem inverse_unit_opposite_weight (ρ ι : R →ₐ[B] T) (χ : Tˣ)
    (u : Rˣ) (hu : (u : R) ∈ weightSpace ρ ι (χ : T)) :
    (↑u⁻¹ : R) ∈ weightSpace ρ ι (↑χ⁻¹ : T) := by
  change ρ (↑u⁻¹ : R) = ι (↑u⁻¹ : R) * (↑χ⁻¹ : T)
  apply (u.isUnit.map ρ).mul_left_cancel
  have hρ : ρ (u : R) = ι (u : R) * (χ : T) := hu
  have hι : ι (u : R) * ι (↑u⁻¹ : R) = 1 := by rw [← map_mul]; simp
  calc
    ρ (u : R) * ρ (↑u⁻¹ : R) = 1 := by rw [← map_mul]; simp
    _ = (ι (u : R) * ι (↑u⁻¹ : R)) * ((χ : T) * (↑χ⁻¹ : T)) := by
      simp only [hι, Units.mul_inv, mul_one]
    _ = (ι (u : R) * (χ : T)) * (ι (↑u⁻¹ : R) * (↑χ⁻¹ : T)) := by ac_rfl
    _ = ρ (u : R) * (ι (↑u⁻¹ : R) * (↑χ⁻¹ : T)) := by rw [hρ]

/-- Quotients of units of the same weight are invariant. This does not
identify the invariant ring with the base; that is a separate hypothesis. -/
theorem same_weight_unit_ratio_fixed (ρ ι : R →ₐ[B] T) (χ : Tˣ)
    (u v : Rˣ) (hu : (u : R) ∈ weightSpace ρ ι (χ : T))
    (hv : (v : R) ∈ weightSpace ρ ι (χ : T)) :
    (↑(u * v⁻¹) : R) ∈ weightSpace ρ ι 1 := by
  simpa only [Units.val_mul, Units.mul_inv] using
    weightSpace_mul ρ ι hu (inverse_unit_opposite_weight ρ ι χ v hv)

/-- With injective base inclusion and invariants equal to its image, two
same-weight units differ by a UNIT of the base ring. Both directions of
the ratio are used; no field hypothesis is needed. -/
theorem same_weight_units_differ_by_base_unit (ρ ι : R →ₐ[B] T) (χ : Tˣ)
    (hinj : Function.Injective (algebraMap B R))
    (hfixed : ∀ r : R, ρ r = ι r → ∃ b : B, algebraMap B R b = r)
    (u v : Rˣ) (hu : (u : R) ∈ weightSpace ρ ι (χ : T))
    (hv : (v : R) ∈ weightSpace ρ ι (χ : T)) :
    ∃ b : B, IsUnit b ∧ (u : R) = algebraMap B R b * (v : R) := by
  have huv := same_weight_unit_ratio_fixed ρ ι χ u v hu hv
  have hvu := same_weight_unit_ratio_fixed ρ ι χ v u hv hu
  obtain ⟨b, hb⟩ := hfixed (u * v⁻¹ : Rˣ) (by
    simpa only [mem_weightSpace, mul_one] using huv)
  obtain ⟨c, hc⟩ := hfixed (v * u⁻¹ : Rˣ) (by
    simpa only [mem_weightSpace, mul_one] using hvu)
  have hbc : b * c = 1 := by
    apply hinj
    rw [map_mul, hb, hc, map_one, ← Units.val_mul]
    simp only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, Units.val_one]
  refine ⟨b, isUnit_of_mul_eq_one b c hbc, ?_⟩
  rw [hb, Units.val_mul]
  simp only [mul_assoc, Units.inv_mul, mul_one]

end Weights

end StrictEUnit

#print axioms StrictEUnit.weightSpace_mul
#print axioms StrictEUnit.weightSpaceBaseChangeEquiv
#print axioms StrictEUnit.weightSpaceBaseChangeEquiv_tmul
#print axioms StrictEUnit.opposite_weight_mul_fixed
#print axioms StrictEUnit.oppositeWeightPairing_tmul
#print axioms StrictEUnit.scalarsFixedEquiv
#print axioms StrictEUnit.scalarWeightPairing_tmul
#print axioms StrictEUnit.inverse_unit_opposite_weight
#print axioms StrictEUnit.same_weight_unit_ratio_fixed
#print axioms StrictEUnit.same_weight_units_differ_by_base_unit
