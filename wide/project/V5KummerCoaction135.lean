import V5KummerBaseChangeChart135
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
set_option maxHeartbeats 600000
set_option maxRecDepth 1600
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
local instance algebraSMulCommCoact135 (A B C : Type*) [CommRing A] [CommRing B]
    [CommRing C] [Algebra A C] [Algebra B C] : SMulCommClass A B C :=
  ⟨fun a b c => by simp only [Algebra.smul_def]; exact mul_left_comm _ _ _⟩
variable {k T L R N : Type*}
  [CommRing k] [CommRing T] [CommRing L] [CommRing R] [CommRing N]
  [Algebra k T] [Algebra k L] [Algebra k R] [Algebra k N]
  [Algebra T L] [Algebra T R]
  [IsScalarTower k T L] [IsScalarTower k T R]

def v5KummerCoaction135 (ρ : R →ₐ[T] R ⊗[k] N) :
    L ⊗[T] R →ₐ[L] (L ⊗[T] R) ⊗[k] N :=
  (v5KummerTensorAssoc135 (k := k) (T := T) (L := L) (R := R) (N := N)).symm.toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id L L) ρ)

@[simp] theorem v5KummerCoaction135_tmul (ρ : R →ₐ[T] R ⊗[k] N) (l : L) (r : R) :
    v5KummerCoaction135 ρ (l ⊗ₜ[T] r) =
      (v5KummerTensorAssoc135 (k := k) (T := T) (L := L) (R := R) (N := N)).symm
        (l ⊗ₜ[T] ρ r) := rfl

theorem v5KummerBaseChangeChart135_right
    (e : R ⊗[T] R ≃ₐ[R] R ⊗[k] N) (ρ : R →ₐ[T] R ⊗[k] N)
    (he : ∀ a b, e (a ⊗ₜ[T] b) = a • ρ b) (x : L ⊗[T] R) :
    v5KummerBaseChangeChart135 e ((1 : L ⊗[T] R) ⊗ₜ[L] x) = v5KummerCoaction135 ρ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.tmul_zero, map_zero]
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul l r =>
    change v5KummerBaseChangeRingChart135 e ((1 : L ⊗[T] R) ⊗ₜ[L] (l ⊗ₜ[T] r)) = _
    rw [v5KummerBaseChangeRingChart135_tmul, v5KummerCoaction135_tmul]
    have hl : l • (1 : L ⊗[T] R) = l ⊗ₜ[T] (1 : R) := by
      simp only [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hl, Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    change (v5KummerTensorAssoc135 (k := k) (T := T) (L := L) (R := R) (N := N)).symm
      (l ⊗ₜ[T] e ((1 : R) ⊗ₜ[T] r)) = _
    rw [he, one_smul]

theorem v5KummerBaseChangeChart135_tmul
    (e : R ⊗[T] R ≃ₐ[R] R ⊗[k] N) (ρ : R →ₐ[T] R ⊗[k] N)
    (he : ∀ a b, e (a ⊗ₜ[T] b) = a • ρ b) (x y : L ⊗[T] R) :
    v5KummerBaseChangeChart135 e (x ⊗ₜ[L] y) = x • v5KummerCoaction135 ρ y := by
  have h : x ⊗ₜ[L] y = x • ((1 : L ⊗[T] R) ⊗ₜ[L] y) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h, map_smul, v5KummerBaseChangeChart135_right e ρ he]
end StrictEUnit
#print axioms StrictEUnit.v5KummerCoaction135
#print axioms StrictEUnit.v5KummerBaseChangeChart135_tmul
