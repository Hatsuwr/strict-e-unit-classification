import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.TensorProduct.Basic

noncomputable section
open scoped TensorProduct
namespace StrictEUnit
open TensorProduct

/-- Linear equalizers transport along two compatible linear charts. -/
def v5LinearEqualizerTransport {A X Y X' Y' : Type*} [CommRing A]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup X'] [AddCommGroup Y']
    [Module A X] [Module A Y] [Module A X'] [Module A Y']
    (e : X ≃ₗ[A] X') (E : Y ≃ₗ[A] Y')
    (f g : X →ₗ[A] Y) (f' g' : X' →ₗ[A] Y')
    (hf : ∀ x, E (f x) = f' (e x)) (hg : ∀ x, E (g x) = g' (e x)) :
    LinearMap.eqLocus f g ≃ₗ[A] LinearMap.eqLocus f' g' := by
  let m : LinearMap.eqLocus f g →ₗ[A] LinearMap.eqLocus f' g' :=
    (e.toLinearMap.comp (LinearMap.eqLocus f g).subtype).codRestrict _ (fun x => by
      change f' (e x.val) = g' (e x.val)
      rw [← hf, ← hg]
      exact congrArg E x.property)
  refine LinearEquiv.ofBijective m ⟨?_, ?_⟩
  · intro x y h
    exact Subtype.ext (e.injective (congrArg Subtype.val h))
  · intro z
    have hp : f (e.symm z.val) = g (e.symm z.val) := by
      apply E.injective
      rw [hf, hg, e.apply_symm_apply]
      exact z.property
    exact ⟨⟨e.symm z.val, hp⟩, Subtype.ext (e.apply_symm_apply _)⟩

section Weight
variable {k B R H A : Type*} [CommRing k] [CommRing B] [CommRing R]
    [CommRing H] [CommRing A] [Algebra k B] [Algebra k R] [Algebra B R]
    [IsScalarTower k B R] [Algebra k H] [Algebra B A]

/-- The weight map is linear, not generally an algebra homomorphism. -/
def v5WeightTensorMap (χ : H) : R →ₗ[B] R ⊗[k] H where
  toFun x := x ⊗ₜ[k] χ
  map_add' x y := TensorProduct.add_tmul x y χ
  map_smul' b x := TensorProduct.smul_tmul' b x χ

@[simp] theorem v5WeightTensorMap_apply (χ : H) (x : R) :
    v5WeightTensorMap (B := B) χ x = x ⊗ₜ[k] χ := rfl

/-- The weight-character module, defined by its literal equation. -/
def v5WeightSpace (ρ : R →ₗ[B] R ⊗[k] H) (χ : H) : Submodule B R :=
  LinearMap.eqLocus ρ (v5WeightTensorMap χ)

@[simp] theorem v5WeightSpace_mem (ρ : R →ₗ[B] R ⊗[k] H) (χ : H) (x : R) :
    x ∈ v5WeightSpace ρ χ ↔ ρ x = x ⊗ₜ[k] χ := Iff.rfl

/-- Flat scalar extension preserves the exact weight equation. -/
def v5WeightSpaceBaseChange [Module.Flat B A]
    (ρ : R →ₗ[B] R ⊗[k] H) (χ : H) :
    A ⊗[B] v5WeightSpace ρ χ ≃ₗ[A]
      LinearMap.eqLocus (AlgebraTensorModule.lTensor A A ρ)
        (AlgebraTensorModule.lTensor A A (v5WeightTensorMap χ)) :=
  LinearMap.tensorEqLocusEquiv A A ρ (v5WeightTensorMap χ)

@[simp] theorem v5WeightSpaceBaseChange_tmul [Module.Flat B A]
    (ρ : R →ₗ[B] R ⊗[k] H) (χ : H) (a : A) (x : v5WeightSpace ρ χ) :
    (v5WeightSpaceBaseChange (A := A) ρ χ (a ⊗ₜ[B] x) : A ⊗[B] R) =
      a ⊗ₜ[B] (x : R) := rfl
end Weight

section Chart
variable {B k A R T H V : Type*} [CommRing B] [Field k] [CommRing A]
    [AddCommGroup R] [AddCommGroup T] [AddCommGroup H] [AddCommGroup V]
    [Module B R] [Module B T] [Module k H] [Module k V]
    [Algebra B A] [Algebra k A]

/-- A split rank-one model descends through exact linear equalizer squares.
This applies to weight maps even when they do not preserve products or one. -/
def v5SplitLinearEqualizerBaseChange [Module.Flat B A]
    (f g : R →ₗ[B] T) (φ ψ : H →ₗ[k] V)
    (e : A ⊗[B] R ≃ₗ[A] A ⊗[k] H) (E : A ⊗[B] T ≃ₗ[A] A ⊗[k] V)
    (hf : ∀ x, E (AlgebraTensorModule.lTensor A A f x) =
      AlgebraTensorModule.lTensor A A φ (e x))
    (hg : ∀ x, E (AlgebraTensorModule.lTensor A A g x) =
      AlgebraTensorModule.lTensor A A ψ (e x))
    (line : LinearMap.eqLocus φ ψ ≃ₗ[k] k) :
    A ⊗[B] LinearMap.eqLocus f g ≃ₗ[A] A := by
  let h := v5LinearEqualizerTransport e E
    (AlgebraTensorModule.lTensor A A f) (AlgebraTensorModule.lTensor A A g)
    (AlgebraTensorModule.lTensor A A φ) (AlgebraTensorModule.lTensor A A ψ) hf hg
  exact (LinearMap.tensorEqLocusEquiv A A f g).trans
    (h.trans ((LinearMap.tensorEqLocusEquiv A A φ ψ).symm.trans
      ((AlgebraTensorModule.congr (LinearEquiv.refl A A) line).trans
        (AlgebraTensorModule.rid k A A))))
end Chart
end StrictEUnit
#print axioms StrictEUnit.v5LinearEqualizerTransport
#print axioms StrictEUnit.v5WeightTensorMap
#print axioms StrictEUnit.v5WeightSpaceBaseChange
#print axioms StrictEUnit.v5WeightSpaceBaseChange_tmul
#print axioms StrictEUnit.v5SplitLinearEqualizerBaseChange
