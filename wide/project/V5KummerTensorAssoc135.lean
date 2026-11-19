import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
noncomputable section
set_option maxHeartbeats 600000
set_option maxRecDepth 1600
open scoped TensorProduct
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
local instance algebraSMulComm135 (A B C : Type*) [CommRing A] [CommRing B]
    [CommRing C] [Algebra A C] [Algebra B C] : SMulCommClass A B C :=
  ⟨fun a b c => by simp only [Algebra.smul_def]; exact mul_left_comm _ _ _⟩
variable {k T L R N : Type*}
  [CommRing k] [CommRing T] [CommRing L] [CommRing R] [CommRing N]
  [Algebra k T] [Algebra k L] [Algebra k R] [Algebra k N]
  [Algebra T L] [Algebra T R]
  [IsScalarTower k T L] [IsScalarTower k T R]

def v5KummerTensorAssoc135 :
    (L ⊗[T] R) ⊗[k] N ≃ₐ[L] L ⊗[T] (R ⊗[k] N) := by
  let e := TensorProduct.AlgebraTensorModule.assoc k T L L R N
  apply AlgEquiv.ofLinearEquiv e
  · rfl
  · apply LinearMap.map_mul_of_map_mul_tmul
    intro x y n m
    induction x using TensorProduct.induction_on with
    | zero => simp only [LinearEquiv.coe_coe, zero_mul, mul_zero, TensorProduct.zero_tmul, e.map_zero]
    | add x y hx hy =>
      simp only [LinearEquiv.coe_coe] at hx hy
      simp only [LinearEquiv.coe_coe, add_mul, e.map_add, TensorProduct.add_tmul, hx, hy]
    | tmul l r =>
      induction y using TensorProduct.induction_on with
      | zero => simp only [LinearEquiv.coe_coe, zero_mul, mul_zero, TensorProduct.zero_tmul, e.map_zero]
      | add x y hx hy =>
        simp only [LinearEquiv.coe_coe] at hx hy
        simp only [LinearEquiv.coe_coe, mul_add, e.map_add, TensorProduct.add_tmul, hx, hy]
      | tmul l' r' =>
        simp only [LinearEquiv.coe_coe]
        rw [Algebra.TensorProduct.tmul_mul_tmul]
        change (l * l') ⊗ₜ[T] ((r * r') ⊗ₜ[k] (n * m)) =
          (l ⊗ₜ[T] (r ⊗ₜ[k] n)) * (l' ⊗ₜ[T] (r' ⊗ₜ[k] m))
        rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]

@[simp] theorem v5KummerTensorAssoc135_tmul (l : L) (r : R) (n : N) :
    v5KummerTensorAssoc135 ((l ⊗ₜ[T] r) ⊗ₜ[k] n) = l ⊗ₜ[T] (r ⊗ₜ[k] n) := rfl

@[simp] theorem v5KummerTensorAssoc135_symm_tmul (l : L) (r : R) (n : N) :
    (v5KummerTensorAssoc135 (k := k) (T := T) (L := L) (R := R) (N := N)).symm (l ⊗ₜ[T] (r ⊗ₜ[k] n)) = (l ⊗ₜ[T] r) ⊗ₜ[k] n := rfl

end StrictEUnit
#print axioms StrictEUnit.v5KummerTensorAssoc135
