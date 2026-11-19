import Mathlib.RingTheory.Unramified.Field
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Flat.Basic

noncomputable section
open scoped TensorProduct
namespace StrictEUnit

/-- An essentially finite-type separable field extension stays reduced after
tensoring with a domain. Embed the domain into its fraction field, where
unramified base change supplies reducedness. -/
theorem v5_separable_tensor_domain_reduced
    (F L D : Type*) [Field F] [Field L] [CommRing D] [IsDomain D]
    [Algebra F L] [Algebra F D]
    [Algebra.IsSeparable F L] [Algebra.EssFiniteType F L] :
    IsReduced (D ⊗[F] L) := by
  let Q := FractionRing D
  letI : Algebra.FormallyUnramified F L :=
    Algebra.FormallyUnramified.of_isSeparable F L
  letI : IsReduced (Q ⊗[F] L) :=
    Algebra.FormallyUnramified.isReduced_of_field Q (Q ⊗[F] L)
  let j : D →ₐ[F] Q := IsScalarTower.toAlgHom F D Q
  let f : D ⊗[F] L →ₐ[F] Q ⊗[F] L :=
    Algebra.TensorProduct.map j (AlgHom.id F L)
  have hj : Function.Injective j := IsFractionRing.injective D Q
  have hf : Function.Injective f :=
    TensorProduct.map_injective_of_flat_flat j.toLinearMap (AlgHom.id F L).toLinearMap
      hj Function.injective_id
  exact isReduced_of_injective f hf

/-- The field-tensor reducedness bridge after choosing a suitable
intermediate field. The pure-transcendental tensor domain hypothesis is
kept separate from the separable algebraic argument. -/
theorem v5_tensor_reduced_of_intermediate_separable
    (K F E₁ E₂ : Type*) [Field K] [Field F] [Field E₁] [Field E₂]
    [Algebra K F] [Algebra K E₁] [Algebra K E₂] [Algebra F E₁]
    [IsScalarTower K F E₁] [Algebra.IsSeparable F E₁]
    [Algebra.EssFiniteType F E₁] [IsDomain (F ⊗[K] E₂)] :
    IsReduced (E₁ ⊗[K] E₂) := by
  letI : IsReduced ((F ⊗[K] E₂) ⊗[F] E₁) :=
    v5_separable_tensor_domain_reduced F E₁ (F ⊗[K] E₂)
  let c := Algebra.TensorProduct.comm F E₁ (F ⊗[K] E₂)
  letI : IsReduced (E₁ ⊗[F] (F ⊗[K] E₂)) :=
    isReduced_of_injective c.toRingHom c.injective
  let e := Algebra.TensorProduct.cancelBaseChange K F F E₁ E₂
  exact isReduced_of_injective e.symm.toRingHom e.symm.injective

/-- Characteristic zero supplies separability for the finite algebraic
extension remaining after a finite transcendence basis. -/
theorem v5_tensor_reduced_of_intermediate_finite_charZero
    (K F E₁ E₂ : Type*) [Field K] [Field F] [Field E₁] [Field E₂]
    [CharZero F] [Algebra K F] [Algebra K E₁] [Algebra K E₂] [Algebra F E₁]
    [IsScalarTower K F E₁] [FiniteDimensional F E₁]
    [IsDomain (F ⊗[K] E₂)] : IsReduced (E₁ ⊗[K] E₂) :=
  v5_tensor_reduced_of_intermediate_separable K F E₁ E₂

end StrictEUnit
#print axioms StrictEUnit.v5_separable_tensor_domain_reduced
#print axioms StrictEUnit.v5_tensor_reduced_of_intermediate_separable
#print axioms StrictEUnit.v5_tensor_reduced_of_intermediate_finite_charZero
