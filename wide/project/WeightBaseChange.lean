import WeightSpaces

/-!
# Actual weight spaces after algebra base change

This file fills the comparison between the linear equalizer in
`weightSpaceBaseChangeEquiv` and the weight space for the base-changed algebra
maps themselves. The multiplier really is `1 tensor chi`; it is not an
uninterpreted replacement linear map.

The construction is generic. It does not instantiate a geometric torsor,
prove flatness for the manuscript's rings, or provide a trivializing chart.
-/

open scoped TensorProduct
open TensorProduct

noncomputable section

namespace StrictEUnit

variable {B R T : Type*} [CommRing B] [CommRing R] [CommRing T]
  [Algebra B R] [Algebra B T]

/-- The actual extension of a B-algebra map to an A-algebra map. -/
def weightBaseChangeAlgHom (A : Type*) [CommRing A] [Algebra B A]
    (f : R →ₐ[B] T) : A ⊗[B] R →ₐ[A] A ⊗[B] T :=
  Algebra.TensorProduct.map (AlgHom.id A A) f

/-- On pure tensors the extended algebra map fixes the new scalar. -/
@[simp] theorem weightBaseChangeAlgHom_tmul
    (A : Type*) [CommRing A] [Algebra B A]
    (f : R →ₐ[B] T) (a : A) (r : R) :
    weightBaseChangeAlgHom A f (a ⊗ₜ[B] r) = a ⊗ₜ[B] f r := rfl

/-- Its underlying A-linear map is the tensor extension used by the
flat-equalizer theorem. -/
theorem weightBaseChangeAlgHom_toLinearMap
    (A : Type*) [CommRing A] [Algebra B A] (f : R →ₐ[B] T) :
    (weightBaseChangeAlgHom A f).toLinearMap =
      AlgebraTensorModule.lTensor A A f.toLinearMap := by
  apply AlgebraTensorModule.ext
  intro a r
  rfl

/-- Tensor extension of the fixed-multiplier map is multiplication by the
actual extended multiplier `1 tensor chi`, after extending the algebra map. -/
theorem tensor_fixed_multiplier_eq
    (A : Type*) [CommRing A] [Algebra B A]
    (ι : R →ₐ[B] T) (χ : T) :
    AlgebraTensorModule.lTensor A A
        ((LinearMap.mulRight B χ).comp ι.toLinearMap) =
      (LinearMap.mulRight A ((1 : A) ⊗ₜ[B] χ)).comp
        (weightBaseChangeAlgHom A ι).toLinearMap := by
  apply AlgebraTensorModule.ext
  intro a r
  change a ⊗ₜ[B] (ι r * χ) =
    (a ⊗ₜ[B] ι r) * ((1 : A) ⊗ₜ[B] χ)
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

/-- The tensor equalizer is exactly the genuine weight submodule of the
base-changed algebra, with its extended multiplier. No flatness is needed
for this identification; flatness is needed for preservation of the equalizer. -/
theorem tensor_weight_eqLocus_eq_actual
    (A : Type*) [CommRing A] [Algebra B A]
    (ρ ι : R →ₐ[B] T) (χ : T) :
    LinearMap.eqLocus (AlgebraTensorModule.lTensor A A ρ.toLinearMap)
        (AlgebraTensorModule.lTensor A A
          ((LinearMap.mulRight B χ).comp ι.toLinearMap)) =
      weightSpace (weightBaseChangeAlgHom A ρ) (weightBaseChangeAlgHom A ι)
        ((1 : A) ⊗ₜ[B] χ) := by
  simp only [weightSpace, tensor_fixed_multiplier_eq, weightBaseChangeAlgHom_toLinearMap]

/-- Flat base change preserves the actual weight space, interpreted using
the actual base-changed algebra maps and the element `1 tensor chi`. -/
noncomputable def actualWeightSpaceBaseChangeEquiv
    (A : Type*) [CommRing A] [Algebra B A] [Module.Flat B A]
    (ρ ι : R →ₐ[B] T) (χ : T) :
    A ⊗[B] weightSpace ρ ι χ ≃ₗ[A]
      weightSpace (weightBaseChangeAlgHom A ρ) (weightBaseChangeAlgHom A ι)
        ((1 : A) ⊗ₜ[B] χ) :=
  (weightSpaceBaseChangeEquiv ρ ι χ A).trans
    (LinearEquiv.ofEq _ _ (tensor_weight_eqLocus_eq_actual A ρ ι χ))

/-- The upgraded equivalence remains the canonical pure-tensor map. -/
theorem actualWeightSpaceBaseChangeEquiv_tmul
    (A : Type*) [CommRing A] [Algebra B A] [Module.Flat B A]
    (ρ ι : R →ₐ[B] T) (χ : T) (a : A) (x : weightSpace ρ ι χ) :
    ((actualWeightSpaceBaseChangeEquiv A ρ ι χ) (a ⊗ₜ[B] x) : A ⊗[B] R) =
      a ⊗ₜ[B] (x : R) := rfl

end StrictEUnit

#print axioms StrictEUnit.weightBaseChangeAlgHom_tmul
#print axioms StrictEUnit.weightBaseChangeAlgHom_toLinearMap
#print axioms StrictEUnit.tensor_fixed_multiplier_eq
#print axioms StrictEUnit.tensor_weight_eqLocus_eq_actual
#print axioms StrictEUnit.actualWeightSpaceBaseChangeEquiv
#print axioms StrictEUnit.actualWeightSpaceBaseChangeEquiv_tmul
