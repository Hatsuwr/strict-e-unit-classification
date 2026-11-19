import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Tower

noncomputable section
open scoped TensorProduct
namespace StrictEUnit

/-- Faithful flatness, not just flatness, descends along faithfully flat
scalar extension. -/
theorem v5_faithfullyFlat_of_tensor (A S M : Type*) [CommRing A] [CommRing S]
    [Algebra A S] [AddCommGroup M] [Module A M]
    [Module.FaithfullyFlat A S] [Module.FaithfullyFlat S (S ⊗[A] M)] :
    Module.FaithfullyFlat A M := by
  refine (Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality A M).mpr
    ⟨Module.Flat.of_flat_tensorProduct A M S, ?_⟩
  intro N _ _ hN
  have h₁ : Subsingleton (S ⊗[A] (N ⊗[A] M)) := by
    letI := hN
    infer_instance
  have h₂ : Subsingleton ((S ⊗[A] N) ⊗[S] (S ⊗[A] M)) :=
    (TensorProduct.AlgebraTensorModule.distribBaseChange A S N M).symm.injective.subsingleton
  letI := h₂
  have h₃ : Subsingleton (S ⊗[A] N) :=
    Module.FaithfullyFlat.rTensor_reflects_triviality S (S ⊗[A] M) (S ⊗[A] N)
  letI := h₃
  exact Module.FaithfullyFlat.lTensor_reflects_triviality A S N

/-- A nonzero vector space over a field is faithfully flat. -/
theorem v5_faithfullyFlat_of_field_nontrivial (k M : Type*) [Field k]
    [AddCommGroup M] [Module k M] [Nontrivial M] :
    Module.FaithfullyFlat k M := by
  refine (Module.FaithfullyFlat.iff_flat_and_proper_ideal k M).mpr ⟨inferInstance, ?_⟩
  intro I hI
  have h : I = ⊥ := (eq_bot_or_eq_top I).resolve_right hI
  subst I
  simp

open Algebra.TensorProduct

/-- A tensor product commutes with finite products on its left as well.
The coefficient algebra is retained on the base field for easy transport. -/
def v5TensorPiLeft {k R N J : Type*} [CommRing k] [CommRing R] [CommRing N]
    [Algebra k R] [Algebra k N] [Fintype J] [DecidableEq J] :
    (J → R) ⊗[k] N ≃ₐ[k] (J → R ⊗[k] N) :=
  (Algebra.TensorProduct.comm k (J → R) N).trans
    ((Algebra.TensorProduct.piRight k k N (fun _ : J => R)).trans
      (AlgEquiv.piCongrRight fun _ : J => Algebra.TensorProduct.comm k N R))

@[simp]
theorem v5TensorPiLeft_tmul {k R N J : Type*} [CommRing k] [CommRing R] [CommRing N]
    [Algebra k R] [Algebra k N] [Fintype J] [DecidableEq J]
    (a : J → R) (n : N) (j : J) :
    v5TensorPiLeft (k := k) (R := R) (N := N) (J := J) (a ⊗ₜ[k] n) j = (a j ⊗ₜ[k] n) := rfl

/-- An algebra which splits after base change into the same nonzero
geometric factor on every component is faithfully flat over the split base.
The scalar rule states that the product chart really is a chart over that base. -/
theorem v5_faithfullyFlat_over_split_chart {k R N A C J : Type*}
    [Field k] [CommRing R] [CommRing N] [CommRing A] [CommRing C] [Nontrivial N]
    [Algebra k R] [Algebra k N] [Algebra k A] [Algebra A C]
    [Fintype J] [DecidableEq J]
    (E : A ≃ₐ[k] (J → R)) (F : C ≃+* (J → R ⊗[k] N))
    (h : ∀ a j, F (algebraMap A C a) j = E a j ⊗ₜ[k] (1 : N)) :
    Module.FaithfullyFlat A C := by
  let e₁ : A ⊗[k] N ≃ₐ[k] (J → R) ⊗[k] N :=
    Algebra.TensorProduct.congr E (AlgEquiv.refl : N ≃ₐ[k] N)
  let e₂ : (J → R) ⊗[k] N ≃ₐ[k] (J → R ⊗[k] N) := v5TensorPiLeft
  let e := F.trans (e₁.trans e₂).toRingEquiv.symm
  let eₐ : C ≃ₐ[A] A ⊗[k] N := AlgEquiv.ofRingEquiv (f := e) (by
    intro a
    apply (e₁.trans e₂).injective
    change (e₁.trans e₂) ((e₁.trans e₂).symm (F (algebraMap A C a))) =
      (e₁.trans e₂) (a ⊗ₜ[k] 1)
    rw [AlgEquiv.apply_symm_apply]
    funext j
    exact h a j)
  letI : Module.FaithfullyFlat k N := v5_faithfullyFlat_of_field_nontrivial k N
  exact Module.FaithfullyFlat.of_linearEquiv A _ eₐ.toLinearEquiv


section BaseChange

variable {B T R : Type*} [CommRing B] [CommRing T] [CommRing R]
    [Algebra B T] [Algebra B R] [Algebra T R] [IsScalarTower B T R]

/-- Extend the base from T to T tensor_B R and identify the resulting module
with the original two R factors over B, retaining the scalar map explicitly. -/
def v5RelativeChangeScalar : (T ⊗[B] R) →+* (R ⊗[B] R) :=
  (Algebra.TensorProduct.map (AlgHom.id R R)
    ((Algebra.ofId T R).restrictScalars B)).toRingHom.comp
    (Algebra.TensorProduct.comm B T R).toRingEquiv.toRingHom

def v5RelativeChangeEquiv :
    letI : Algebra (T ⊗[B] R) (R ⊗[B] R) := v5RelativeChangeScalar.toAlgebra
    ((T ⊗[B] R) ⊗[T] R) ≃ₐ[T ⊗[B] R] (R ⊗[B] R) := by
  letI : Algebra (T ⊗[B] R) (R ⊗[B] R) := v5RelativeChangeScalar.toAlgebra
  let e₁ := Algebra.TensorProduct.comm T (T ⊗[B] R) R
  let e₂ := Algebra.TensorProduct.cancelBaseChange B T T R R
  let e₃ := Algebra.TensorProduct.comm B R R
  let e := e₁.toRingEquiv.trans (e₂.toRingEquiv.trans e₃.toRingEquiv)
  refine AlgEquiv.ofRingEquiv (f := e) (fun s => ?_)
  let f : (T ⊗[B] R) →+* (R ⊗[B] R) := e.toRingHom.comp
    (algebraMap (T ⊗[B] R) ((T ⊗[B] R) ⊗[T] R))
  let g : (T ⊗[B] R) →+* (R ⊗[B] R) := v5RelativeChangeScalar
  change f s = g s
  induction s using TensorProduct.induction_on with
  | zero => rw [f.map_zero, g.map_zero]
  | add a b ha hb => rw [f.map_add, g.map_add, ha, hb]
  | tmul t r =>
    change e₃ (e₂ (e₁ ((t ⊗ₜ[B] r) ⊗ₜ[T] (1 : R)))) = _
    rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.cancelBaseChange_tmul,
      Algebra.TensorProduct.comm_tmul, Algebra.smul_def, mul_one]
    rfl

/-- To prove R faithfully flat over T, it is enough that the two R factors
over B be faithfully flat over the base-change T⊗₍B₎R with its natural map. -/
theorem v5_relative_faithfullyFlat_of_double [Module.FaithfullyFlat B R]
    (h : letI : Algebra (T ⊗[B] R) (R ⊗[B] R) :=
        v5RelativeChangeScalar.toAlgebra
      Module.FaithfullyFlat (T ⊗[B] R) (R ⊗[B] R)) :
    Module.FaithfullyFlat T R := by
  letI : Algebra (T ⊗[B] R) (R ⊗[B] R) := v5RelativeChangeScalar.toAlgebra
  letI : Module.FaithfullyFlat (T ⊗[B] R) (R ⊗[B] R) := h
  letI : Module.FaithfullyFlat (T ⊗[B] R) ((T ⊗[B] R) ⊗[T] R) :=
    Module.FaithfullyFlat.of_linearEquiv _ _ v5RelativeChangeEquiv.toLinearEquiv
  exact v5_faithfullyFlat_of_tensor T (T ⊗[B] R) R

end BaseChange

section ComponentScalarChange

variable {k B T R N J : Type*}
    [Field k] [CommRing B] [CommRing T] [CommRing R] [CommRing N] [Nontrivial N]
    [Algebra k B] [Algebra B T] [Algebra B R] [Algebra T R] [IsScalarTower B T R]
    [Algebra k T] [Algebra k R] [Algebra k N] [IsScalarTower k B T] [IsScalarTower k B R]
    [Fintype J] [DecidableEq J]

/-- A product chart of the own torsor proves faithful flatness over the
fixed subalgebra once its scalar restriction is checked on pure tensors. -/
theorem v5_relative_faithfullyFlat_of_component_chart [Module.FaithfullyFlat B R]
    (E : T ⊗[B] R ≃ₐ[k] (J → R)) (F : R ⊗[B] R ≃+* (J → R ⊗[k] N))
    (h : ∀ t r j, F (r ⊗ₜ[B] algebraMap T R t) j = E (t ⊗ₜ[B] r) j ⊗ₜ[k] (1 : N)) :
    Module.FaithfullyFlat T R := by
  apply v5_relative_faithfullyFlat_of_double (B := B)
  letI : Algebra (T ⊗[B] R) (R ⊗[B] R) := v5RelativeChangeScalar.toAlgebra
  refine v5_faithfullyFlat_over_split_chart E F (fun a j => ?_)
  let l : (T ⊗[B] R) →+* R ⊗[k] N :=
    (Pi.evalRingHom (fun _ : J => R ⊗[k] N) j).comp
      (F.toRingHom.comp v5RelativeChangeScalar)
  let r : (T ⊗[B] R) →+* R ⊗[k] N :=
    (algebraMap R (R ⊗[k] N)).comp
      ((Pi.evalRingHom (fun _ : J => R) j).comp E.toRingEquiv.toRingHom)
  change l a = r a
  induction a using TensorProduct.induction_on with
  | zero => rw [l.map_zero, r.map_zero]
  | add a b ha hb => rw [l.map_add, r.map_add, ha, hb]
  | tmul t u => exact h t u j

end ComponentScalarChange
end StrictEUnit
#print axioms StrictEUnit.v5_faithfullyFlat_of_tensor
#print axioms StrictEUnit.v5_faithfullyFlat_of_field_nontrivial
#print axioms StrictEUnit.v5TensorPiLeft
#print axioms StrictEUnit.v5TensorPiLeft_tmul
#print axioms StrictEUnit.v5_faithfullyFlat_over_split_chart
#print axioms StrictEUnit.v5RelativeChangeScalar
#print axioms StrictEUnit.v5RelativeChangeEquiv
#print axioms StrictEUnit.v5_relative_faithfullyFlat_of_double
#print axioms StrictEUnit.v5_relative_faithfullyFlat_of_component_chart
