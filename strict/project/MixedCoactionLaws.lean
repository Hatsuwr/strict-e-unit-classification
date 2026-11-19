import MixedCoactionBaseChange

/-! Transport of the actual mixed-base coassociativity law through the
proved scalar-extension tensor equivalences. -/
open scoped TensorProduct
open TensorProduct
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k B R H : Type*} [CommRing k] [CommRing B] [CommRing R] [CommRing H]
  [Algebra k B] [Algebra B R] [Algebra k R] [IsScalarTower k B R]
section Tensor
variable [Algebra k H]

def mixedCoactionTripleCancel :
    R ⊗[B] ((B ⊗[k] H) ⊗[B] (B ⊗[k] H)) ≃ₐ[R] R ⊗[k] (H ⊗[k] H) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl (R:=R) (A₁:=R))
    (algebraTensorBaseChangeEquiv (k:=k) B H H)).trans
      (Algebra.TensorProduct.cancelBaseChange k B R R (H ⊗[k] H))

@[simp] theorem mixedCoactionTripleCancel_tmul (r:R) (a b:B) (h g:H) :
    mixedCoactionTripleCancel (k:=k) (B:=B)
      (r ⊗ₜ[B] ((a ⊗ₜ[k] h) ⊗ₜ[B] (b ⊗ₜ[k] g))) =
      ((a*b) • r) ⊗ₜ[k] (h ⊗ₜ[k] g) := by
  simp [mixedCoactionTripleCancel]

theorem mixedCoactionTripleCancel_pair (z:R ⊗[k] H) (h:H) :
    mixedCoactionTripleCancel (k:=k) (B:=B)
      (Algebra.TensorProduct.assoc B R (B ⊗[k] H) (B ⊗[k] H)
        ((Algebra.TensorProduct.cancelBaseChange k B B R H).symm z ⊗ₜ[B]
          ((1:B) ⊗ₜ[k] h))) =
      Algebra.TensorProduct.assoc k R H H (z ⊗ₜ[k] h) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [TypedMaps.algEquiv_zero, zero_tmul]
  | add x y hx hy => simp only [TypedMaps.algEquiv_add, add_tmul, hx, hy]
  | tmul r g =>
    simp only [Algebra.TensorProduct.cancelBaseChange_symm_tmul,
      Algebra.TensorProduct.assoc_tmul, mixedCoactionTripleCancel_tmul, one_mul, one_smul]

theorem scalarTargetCoaction_left_leg (ρ:R →ₐ[B] R ⊗[k] H) (z:R ⊗[k] H) :
    mixedCoactionTripleCancel (k:=k) (B:=B)
      (Algebra.TensorProduct.assoc B R (B ⊗[k] H) (B ⊗[k] H)
        (Algebra.TensorProduct.map (scalarTargetCoaction ρ) (AlgHom.id B (B ⊗[k] H))
          ((Algebra.TensorProduct.cancelBaseChange k B B R H).symm z))) =
      Algebra.TensorProduct.assoc k R H H
        (Algebra.TensorProduct.map (ρ.restrictScalars k) (AlgHom.id k H) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [TypedMaps.algEquiv_zero, TypedMaps.algHom_zero]
  | add x y hx hy => simp only [TypedMaps.algEquiv_add, TypedMaps.algHom_add, hx, hy]
  | tmul r h =>
    simp only [Algebra.TensorProduct.cancelBaseChange_symm_tmul,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.restrictScalars_apply]
    exact mixedCoactionTripleCancel_pair (ρ r) h

theorem scalarTargetCoaction_right_pair (r:R) (z:H ⊗[k] H) :
    mixedCoactionTripleCancel (k:=k) (B:=B)
      (r ⊗ₜ[B] (algebraTensorBaseChangeEquiv (k:=k) B H H).symm
        ((1:B) ⊗ₜ[k] z)) = r ⊗ₜ[k] z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
  | tmul h g => simp

end Tensor
section Bialgebra
variable [Bialgebra k H]

theorem scalarTargetCoaction_right_leg (z:R ⊗[k] H) :
    mixedCoactionTripleCancel (k:=k) (B:=B)
      (weightBaseChangeAlgHom R (baseChangeComul (k:=k) (H:=H) B)
        ((Algebra.TensorProduct.cancelBaseChange k B B R H).symm z)) =
      weightBaseChangeAlgHom R (Bialgebra.comulAlgHom k H) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [TypedMaps.algEquiv_zero, TypedMaps.algHom_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r h =>
    simp only [Algebra.TensorProduct.cancelBaseChange_symm_tmul,
      weightBaseChangeAlgHom_tmul, baseChangeComul_tmul]
    exact scalarTargetCoaction_right_pair r _

theorem scalarTargetCoaction_coassoc (ρ:R →ₐ[B] R ⊗[k] H)
    (hc : ∀ r:R, Algebra.TensorProduct.assoc k R H H
      (Algebra.TensorProduct.map (ρ.restrictScalars k) (AlgHom.id k H) (ρ r)) =
      weightBaseChangeAlgHom R (Bialgebra.comulAlgHom k H) (ρ r)) (r:R) :
    Algebra.TensorProduct.assoc B R (B ⊗[k] H) (B ⊗[k] H)
      (Algebra.TensorProduct.map (scalarTargetCoaction ρ) (AlgHom.id B (B ⊗[k] H))
        (scalarTargetCoaction ρ r)) =
      weightBaseChangeAlgHom R (baseChangeComul (k:=k) (H:=H) B)
        (scalarTargetCoaction ρ r) := by
  apply (mixedCoactionTripleCancel (k:=k) (B:=B) (R:=R) (H:=H)).injective
  exact (scalarTargetCoaction_left_leg ρ (ρ r)).trans
    ((hc r).trans (scalarTargetCoaction_right_leg (B:=B) (ρ r)).symm)
end Bialgebra
end StrictEUnit
#print axioms StrictEUnit.mixedCoactionTripleCancel
#print axioms StrictEUnit.mixedCoactionTripleCancel_tmul
#print axioms StrictEUnit.mixedCoactionTripleCancel_pair
#print axioms StrictEUnit.scalarTargetCoaction_left_leg
#print axioms StrictEUnit.scalarTargetCoaction_right_pair
#print axioms StrictEUnit.scalarTargetCoaction_right_leg
#print axioms StrictEUnit.scalarTargetCoaction_coassoc
