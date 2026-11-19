import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Associator

noncomputable section
open scoped TensorProduct
open Algebra.TensorProduct
namespace StrictEUnit
variable {k H T : Type*} [Field k] [CommRing H] [HopfAlgebra k H]
  [CommRing T] [Algebra k T]

private def hopfPair (f g : H →ₐ[k] T) : (H ⊗[k] H) →ₐ[k] T :=
  Algebra.TensorProduct.lift f g (fun _ _ => .all _ _)

@[simp] private theorem hopfPair_tmul (f g : H →ₐ[k] T) (x y : H) :
    hopfPair f g (x ⊗ₜ[k] y) = f x * g y := rfl

/-- The algebra-valued convolution of two coordinate-ring morphisms. -/
def v5HopfConv (f g : H →ₐ[k] T) : H →ₐ[k] T :=
  (hopfPair f g).comp (Bialgebra.comulAlgHom k H)

theorem v5HopfConv_assoc (f g h : H →ₐ[k] T) :
    v5HopfConv (v5HopfConv f g) h = v5HopfConv f (v5HopfConv g h) := by
  let L : (H ⊗[k] H) ⊗[k] H →ₗ[k] T :=
    (Algebra.TensorProduct.lift (hopfPair f g) h (fun _ _ => .all _ _)).toLinearMap
  let R : H ⊗[k] (H ⊗[k] H) →ₗ[k] T :=
    (Algebra.TensorProduct.lift f (hopfPair g h) (fun _ _ => .all _ _)).toLinearMap
  have hLR : L = R.comp (TensorProduct.assoc k H H H).toLinearMap := by
    ext a b c
    simp [L, R, mul_assoc]
  have hleft : (hopfPair (v5HopfConv f g) h).toLinearMap =
      L.comp ((Coalgebra.comul (R := k) (A := H)).rTensor H) := by
    ext a b
    simp [L, v5HopfConv]
  have hright : (hopfPair f (v5HopfConv g h)).toLinearMap =
      R.comp ((Coalgebra.comul (R := k) (A := H)).lTensor H) := by
    ext a b
    simp [R, v5HopfConv]
  ext a
  change (hopfPair (v5HopfConv f g) h).toLinearMap (Coalgebra.comul a) =
    (hopfPair f (v5HopfConv g h)).toLinearMap (Coalgebra.comul a)
  rw [hleft, hright, hLR]
  exact congrArg R (Coalgebra.coassoc_apply (R := k) a)

theorem v5HopfConv_comp {U : Type*} [CommRing U] [Algebra k U]
    (j : T →ₐ[k] U) (f g : H →ₐ[k] T) :
    j.comp (v5HopfConv f g) = v5HopfConv (j.comp f) (j.comp g) := by
  have hh : j.comp (hopfPair f g) = hopfPair (j.comp f) (j.comp g) := by
    apply AlgHom.toLinearMap_injective
    ext a b
    simp
  unfold v5HopfConv
  rw [← AlgHom.comp_assoc, hh]

private def hopfUnit : H →ₐ[k] T := (Algebra.ofId k T).comp (Bialgebra.counitAlgHom k H)

@[simp] theorem v5HopfConv_unit_left (f : H →ₐ[k] T) :
    v5HopfConv hopfUnit f = f := by
  let L := (Algebra.TensorProduct.lift (Algebra.ofId k T) f
    (fun _ _ => .all _ _)).toLinearMap
  have hl : (hopfPair hopfUnit f).toLinearMap =
      L.comp ((Coalgebra.counit (R := k) (A := H)).rTensor H) := by
    ext a b
    simp [L, hopfUnit]
  ext a
  change (hopfPair hopfUnit f).toLinearMap (Coalgebra.comul a) = f a
  rw [hl, LinearMap.comp_apply, Coalgebra.rTensor_counit_comul]
  simp [L]

@[simp] theorem v5HopfConv_unit_right (f : H →ₐ[k] T) :
    v5HopfConv f hopfUnit = f := by
  let L := (Algebra.TensorProduct.lift f (Algebra.ofId k T)
    (fun _ _ => .all _ _)).toLinearMap
  have hl : (hopfPair f hopfUnit).toLinearMap =
      L.comp ((Coalgebra.counit (R := k) (A := H)).lTensor H) := by
    ext a b
    simp [L, hopfUnit]
  ext a
  change (hopfPair f hopfUnit).toLinearMap (Coalgebra.comul a) = f a
  rw [hl, LinearMap.comp_apply, Coalgebra.lTensor_counit_comul]
  simp [L]

variable (s : H →ₐ[k] H) (hs : s.toLinearMap = HopfAlgebra.antipode)

include hs in
private theorem v5HopfConv_antipode_left :
    v5HopfConv s (AlgHom.id k H) = hopfUnit := by
  have hl : (hopfPair s (AlgHom.id k H)).toLinearMap =
      (LinearMap.mul' k H).comp (s.toLinearMap.rTensor H) := by
    ext a b
    simp
  ext a
  change (hopfPair s (AlgHom.id k H)).toLinearMap (Coalgebra.comul a) = _
  rw [hl, hs, LinearMap.comp_apply, HopfAlgebra.mul_antipode_rTensor_comul_apply]
  rfl

include hs in
private theorem v5HopfConv_antipode_right :
    v5HopfConv (AlgHom.id k H) s = hopfUnit := by
  have hl : (hopfPair (AlgHom.id k H) s).toLinearMap =
      (LinearMap.mul' k H).comp (s.toLinearMap.lTensor H) := by
    ext a b
    simp
  ext a
  change (hopfPair (AlgHom.id k H) s).toLinearMap (Coalgebra.comul a) = _
  rw [hl, hs, LinearMap.comp_apply, HopfAlgebra.mul_antipode_lTensor_comul_apply]
  rfl

/-- Pullback by left translation by a rational point. -/
def v5HopfTranslate (p : H →ₐ[k] k) : H →ₐ[k] H :=
  v5HopfConv ((Algebra.ofId k H).comp p) (AlgHom.id k H)

theorem v5HopfTranslate_comp (p q : H →ₐ[k] k) :
    (v5HopfTranslate p).comp (v5HopfTranslate q) = v5HopfTranslate (v5HopfConv q p) := by
  conv => lhs; arg 2; unfold v5HopfTranslate
  rw [v5HopfConv_comp]
  have h₁ : (v5HopfTranslate p).comp ((Algebra.ofId k H).comp q) =
      (Algebra.ofId k H).comp q := by ext x; exact (v5HopfTranslate p).commutes (q x)
  rw [h₁, AlgHom.comp_id]
  unfold v5HopfTranslate
  rw [← v5HopfConv_assoc, v5HopfConv_comp]

theorem v5HopfTranslate_at_counit (p : H →ₐ[k] k) :
    (Bialgebra.counitAlgHom k H).comp (v5HopfTranslate p) = p := by
  unfold v5HopfTranslate
  rw [v5HopfConv_comp, AlgHom.comp_id]
  have h₁ : (Bialgebra.counitAlgHom k H).comp ((Algebra.ofId k H).comp p) = p := by
    ext x
    exact (Bialgebra.counitAlgHom k H).commutes (p x)
  rw [h₁]
  exact v5HopfConv_unit_right p

private theorem v5HopfTranslate_at_unit :
    v5HopfTranslate (Bialgebra.counitAlgHom k H) = AlgHom.id k H :=
  v5HopfConv_unit_left (AlgHom.id k H)

/-- A point whose left translation is inverted by the antipode point. -/
def v5HopfTranslation (p : H →ₐ[k] k) : H ≃ₐ[k] H := by
  have h₁ := congrArg (fun f : H →ₐ[k] H => p.comp f) (v5HopfConv_antipode_left s hs)
  have h₂ := congrArg (fun f : H →ₐ[k] H => p.comp f) (v5HopfConv_antipode_right s hs)
  change p.comp (v5HopfConv s (AlgHom.id k H)) = p.comp hopfUnit at h₁
  change p.comp (v5HopfConv (AlgHom.id k H) s) = p.comp hopfUnit at h₂
  have hp : p.comp hopfUnit = Bialgebra.counitAlgHom k H := by
    ext x; exact p.commutes (Bialgebra.counitAlgHom k H x)
  simp only [v5HopfConv_comp, AlgHom.comp_id, hp] at h₁ h₂
  exact AlgEquiv.ofAlgHom (v5HopfTranslate p) (v5HopfTranslate (p.comp s))
    (by rw [v5HopfTranslate_comp, h₁, v5HopfTranslate_at_unit])
    (by rw [v5HopfTranslate_comp, h₂, v5HopfTranslate_at_unit])

theorem v5HopfTranslation_at_counit (p : H →ₐ[k] k) :
    (Bialgebra.counitAlgHom k H).comp (v5HopfTranslation s hs p).toAlgHom = p :=
  v5HopfTranslate_at_counit p

end StrictEUnit
#print axioms StrictEUnit.v5HopfConv
#print axioms StrictEUnit.v5HopfConv_assoc

#print axioms StrictEUnit.v5HopfConv_comp
#print axioms StrictEUnit.v5HopfTranslate_comp
#print axioms StrictEUnit.v5HopfTranslate_at_counit
#print axioms StrictEUnit.v5HopfTranslation
#print axioms StrictEUnit.v5HopfTranslation_at_counit
