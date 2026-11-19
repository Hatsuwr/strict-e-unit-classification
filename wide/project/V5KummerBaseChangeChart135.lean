import V5KummerTensorAssoc135
noncomputable section
set_option maxHeartbeats 600000
set_option maxRecDepth 1600
open scoped TensorProduct
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
local instance algebraSMulCommBase135 (A B C : Type*) [CommRing A] [CommRing B]
    [CommRing C] [Algebra A C] [Algebra B C] : SMulCommClass A B C :=
  ⟨fun a b c => by simp only [Algebra.smul_def]; exact mul_left_comm _ _ _⟩
variable {k T L R N : Type*}
  [CommRing k] [CommRing T] [CommRing L] [CommRing R] [CommRing N]
  [Algebra k T] [Algebra k L] [Algebra k R] [Algebra k N]
  [Algebra T L] [Algebra T R]
  [IsScalarTower k T L] [IsScalarTower k T R]

def v5KummerBaseChangeRingChart135
    (e : R ⊗[T] R ≃ₐ[R] R ⊗[k] N) :
    (L ⊗[T] R) ⊗[L] (L ⊗[T] R) ≃+* (L ⊗[T] R) ⊗[k] N :=
  (Algebra.TensorProduct.cancelBaseChange T L (L ⊗[T] R) (L ⊗[T] R) R).toRingEquiv.trans
    ((Algebra.TensorProduct.assoc T L R R).toRingEquiv.trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L)
        (e.restrictScalars T)).toRingEquiv.trans
          (v5KummerTensorAssoc135 (k := k) (T := T) (L := L) (R := R) (N := N)).symm.toRingEquiv))

theorem v5KummerBaseChangeRingChart135_tmul
    (e : R ⊗[T] R ≃ₐ[R] R ⊗[k] N) (l : L) (a : R) (y : L ⊗[T] R) :
    v5KummerBaseChangeRingChart135 e (y ⊗ₜ[L] (l ⊗ₜ[T] a)) =
      (v5KummerTensorAssoc135 (k := k) (T := T) (L := L) (R := R) (N := N)).symm
        (Algebra.TensorProduct.map (AlgHom.id L L) (e.restrictScalars T)
          (Algebra.TensorProduct.assoc T L R R ((l • y) ⊗ₜ[T] a))) := rfl

def v5KummerBaseChangeChart135
    (e : R ⊗[T] R ≃ₐ[R] R ⊗[k] N) :
    (L ⊗[T] R) ⊗[L] (L ⊗[T] R) ≃ₐ[L ⊗[T] R] (L ⊗[T] R) ⊗[k] N := by
  apply AlgEquiv.ofRingEquiv (f := v5KummerBaseChangeRingChart135 e)
  intro s
  change v5KummerBaseChangeRingChart135 e (s ⊗ₜ[L] (1 : L ⊗[T] R)) = s ⊗ₜ[k] (1 : N)
  induction s using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.zero_tmul, map_zero]
  | add x y hx hy =>
    rw [TensorProduct.add_tmul, (v5KummerBaseChangeRingChart135 e).map_add, hx, hy,
      TensorProduct.add_tmul]
  | tmul l r =>
    change v5KummerBaseChangeRingChart135 e ((l ⊗ₜ[T] r) ⊗ₜ[L] (1 ⊗ₜ[T] (1 : R))) =
      (l ⊗ₜ[T] r) ⊗ₜ[k] (1 : N)
    rw [v5KummerBaseChangeRingChart135_tmul]
    simp only [one_smul, Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, AlgEquiv.coe_algHom, AlgEquiv.restrictScalars_apply]
    have he : e (r ⊗ₜ[T] (1 : R)) = r ⊗ₜ[k] (1 : N) := e.commutes r
    change (v5KummerTensorAssoc135 (k := k) (T := T) (L := L) (R := R) (N := N)).symm
      (l ⊗ₜ[T] e (r ⊗ₜ[T] (1 : R))) = _
    rw [he, v5KummerTensorAssoc135_symm_tmul]

theorem v5KummerBaseChangeFaithfullyFlat135 [Module.FaithfullyFlat T R] :
    Module.FaithfullyFlat L (L ⊗[T] R) := inferInstance
end StrictEUnit
#print axioms StrictEUnit.v5KummerBaseChangeChart135
#print axioms StrictEUnit.v5KummerBaseChangeFaithfullyFlat135
