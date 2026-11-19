import RegularRepresentation
import WeightBaseChange
import InvariantDescent

/-!
# The actual scalar-extended regular model

The model is A ⊗[k] H, with coaction landing in A ⊗[k] (H ⊗[k] H).
No coalgebra structure on the cover A is assumed. The coaction and character
are the actual scalar extensions of those over k.
-/

open TensorProduct
open scoped TensorProduct
noncomputable section
namespace StrictEUnit

section General

variable {k H : Type*} [CommRing k] [CommRing H] [Algebra k H]
variable (A : Type*) [CommRing A] [Algebra k A]

/-- The scalar extension of a unit is the actual element `1 tensor u`. -/
def extendedUnit (u : Hˣ) : (A ⊗[k] H)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight : H →ₐ[k] A ⊗[k] H).toMonoidHom u

@[simp] theorem extendedUnit_coe (u : Hˣ) :
    (extendedUnit (k := k) A u : A ⊗[k] H) = (1 : A) ⊗ₜ[k] (u : H) := rfl

/-- Scalar extension preserves the actual weight equation. -/
theorem extendedUnit_weight {T : Type*} [CommRing T] [Algebra k T]
    (ρ ι : H →ₐ[k] T) (χ : Tˣ) (u : Hˣ)
    (hu : (u : H) ∈ weightSpace ρ ι (χ : T)) :
    (extendedUnit (k := k) A u : A ⊗[k] H) ∈
      weightSpace (weightBaseChangeAlgHom A ρ) (weightBaseChangeAlgHom A ι)
        (extendedUnit (k := k) A χ : A ⊗[k] T) := by
  change (1 : A) ⊗ₜ[k] ρ (u : H) =
    ((1 : A) ⊗ₜ[k] ι (u : H)) * ((1 : A) ⊗ₜ[k] (χ : T))
  rw [show ρ (u : H) = ι (u : H) * (χ : T) from hu]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

end General

section Regular
variable {k H : Type*} [CommRing k] [CommRing H] [Bialgebra k H]
variable (A : Type*) [CommRing A] [Algebra k A]

/-- A character unit supplies an actual unit in the extended regular model.
No bialgebra structure on A or on the extended ring is postulated. -/
theorem extended_regular_unit_weight (χ : Hˣ)
    (hχ : Coalgebra.comul (R := k) (χ : H) = (χ : H) ⊗ₜ[k] (χ : H)) :
    (extendedUnit (k := k) A χ : A ⊗[k] H) ∈
      weightSpace (weightBaseChangeAlgHom A (Bialgebra.comulAlgHom k H))
        (weightBaseChangeAlgHom A
          (Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] H))
        ((1 : A) ⊗ₜ[k] ((1 : H) ⊗ₜ[k] (χ : H))) := by
  let ψ : (H ⊗[k] H)ˣ :=
    Units.map (Algebra.TensorProduct.includeRight : H →ₐ[k] H ⊗[k] H).toMonoidHom χ
  exact extendedUnit_weight A (Bialgebra.comulAlgHom k H)
    Algebra.TensorProduct.includeLeft ψ χ ((mem_regularWeightSpace _ _).mpr hχ)

/-- The two opposite character spaces of the extended regular model contain
explicit elements whose product is one. -/
theorem extended_regular_opposite_product_one (χ : Hˣ)
    (hχ : Coalgebra.comul (R := k) (χ : H) = (χ : H) ⊗ₜ[k] (χ : H)) :
    ∃ x y : A ⊗[k] H,
      x ∈ weightSpace (weightBaseChangeAlgHom A (Bialgebra.comulAlgHom k H))
        (weightBaseChangeAlgHom A
          (Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] H))
        ((1 : A) ⊗ₜ[k] ((1 : H) ⊗ₜ[k] (χ : H))) ∧
      y ∈ weightSpace (weightBaseChangeAlgHom A (Bialgebra.comulAlgHom k H))
        (weightBaseChangeAlgHom A
          (Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] H))
        ((1 : A) ⊗ₜ[k] ((1 : H) ⊗ₜ[k] (↑χ⁻¹ : H))) ∧ x * y = 1 := by
  refine ⟨extendedUnit (k := k) A χ, extendedUnit (k := k) A χ⁻¹,
    extended_regular_unit_weight A χ hχ,
    extended_regular_unit_weight A χ⁻¹ (inverse_grouplike_unit χ hχ), ?_⟩
  change ((1 : A) ⊗ₜ[k] (χ : H)) * ((1 : A) ⊗ₜ[k] (↑χ⁻¹ : H)) = 1
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Units.mul_inv,
    Algebra.TensorProduct.one_def]

/-- Scalar injectivity for the regular model survives every flat extension. -/
theorem extended_regular_base_injective [Module.Flat k A] :
    Function.Injective (algebraMap A (A ⊗[k] H)) :=
  scalar_inclusion_injective_ascends A (Bialgebra.comulAlgHom k H)
    (Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] H)
    bialgebra_base_injective

/-- The regular model has exactly scalar invariants, also after flat
extension. This is proved from the actual counit calculation. -/
theorem extended_regular_invariants_are_scalars [Module.Flat k A] :
    ∀ x : A ⊗[k] H,
      weightBaseChangeAlgHom A (Bialgebra.comulAlgHom k H) x =
        weightBaseChangeAlgHom A
          (Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] H) x →
      ∃ a : A, algebraMap A (A ⊗[k] H) a = x := by
  apply invariant_image_ascends A
  intro x hx
  exact ⟨Coalgebra.counit (R := k) x, regular_invariants_are_scalars x hx⟩

end Regular
end StrictEUnit
