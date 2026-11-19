import V5MixedComparisonEquiv
import Mathlib.LinearAlgebra.TensorProduct.Tower

open scoped TensorProduct
open TensorProduct
noncomputable section
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 50000

section Cancel
variable {B R K S : Type*} [CommRing B] [CommRing R] [CommRing K] [CommRing S]
  [Algebra B R] [Algebra R K] [Algebra B K] [IsScalarTower B R K] [Algebra B S]

/-- Scalar extension through a marked algebra, as an algebra equivalence. -/
def v5PointedCancelBaseChange : K ⊗[R] (R ⊗[B] S) ≃ₐ[K] K ⊗[B] S := by
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange B R K K S
  refine AlgEquiv.ofLinearEquiv e ?_ ?_
  · change e ((1 : K) ⊗ₜ[R] ((1 : R) ⊗ₜ[B] (1 : S))) = (1 : K) ⊗ₜ[B] (1 : S)
    simp [e, AlgebraTensorModule.cancelBaseChange_tmul]
  · intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [add_mul, map_add, hx, hy]
    | tmul a x =>
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [tmul_add, add_mul, map_add, hx, hy]
      | tmul r s =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => simp only [mul_add, map_add, hx, hy]
        | tmul b y =>
          induction y using TensorProduct.induction_on with
          | zero => simp
          | add x y hx hy => simp only [tmul_add, mul_add, map_add, hx, hy]
          | tmul t u =>
            simp only [Algebra.TensorProduct.tmul_mul_tmul, e,
              AlgebraTensorModule.cancelBaseChange_tmul, Algebra.smul_def, map_mul]
            congr 1 <;> ring

@[simp] theorem v5PointedCancelBaseChange_tmul (a : K) (r : R) (s : S) :
    v5PointedCancelBaseChange (a ⊗ₜ[R] (r ⊗ₜ[B] s)) = (r • a) ⊗ₜ[B] s := rfl

@[simp] theorem v5PointedCancelBaseChange_symm_tmul (a : K) (s : S) :
    (v5PointedCancelBaseChange (B := B) (R := R)).symm (a ⊗ₜ[B] s) =
      a ⊗ₜ[R] ((1 : R) ⊗ₜ[B] s) :=
  AlgebraTensorModule.cancelBaseChange_symm_tmul B R K a s

end Cancel

section Fiber
variable {k B R S C : Type*} [CommRing k] [CommRing B] [CommRing R] [CommRing S] [CommRing C]
 [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
 [Algebra k S] [Algebra B S] [IsScalarTower k B S] [Algebra k C]
 [Algebra R k] [IsScalarTower k R k] [Algebra B k] [IsScalarTower B R k]

/-- Specializing a mixed comparison at the algebraic point R→k identifies
the constant algebra with the actual algebraic fiber of S. -/
def v5MixedPointedFiber (e : R ⊗[k] C ≃ₐ[R] R ⊗[B] S) :
    C ≃ₐ[k] k ⊗[B] S :=
  (Algebra.TensorProduct.lid k C).symm.trans
    ((v5PointedCancelBaseChange (B := k) (R := R) (K := k) (S := C)).symm.trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl (R := k) (A₁ := k)) e).trans
        (v5PointedCancelBaseChange (B := B) (R := R) (K := k) (S := S))))

@[simp] theorem v5MixedPointedFiber_apply
    (e : R ⊗[k] C ≃ₐ[R] R ⊗[B] S) (c : C) :
    v5MixedPointedFiber e c =
      v5PointedCancelBaseChange ((1 : k) ⊗ₜ[R] e ((1 : R) ⊗ₜ[k] c)) := by
  simp only [v5MixedPointedFiber, AlgEquiv.trans_apply,
    Algebra.TensorProduct.lid_symm_apply, v5PointedCancelBaseChange_symm_tmul]
  rfl

/-- The scalar in the specialized comparison is evaluated by the actual
mark R→k; no evaluation of arbitrary Laurent series is used. -/
theorem v5MixedPointedFiber_of_pure
    (e : R ⊗[k] C ≃ₐ[R] R ⊗[B] S) (c : C) (r : R) (s : S)
    (h : e ((1 : R) ⊗ₜ[k] c) = r ⊗ₜ[B] s) :
    v5MixedPointedFiber e c = algebraMap R k r ⊗ₜ[B] s := by
  rw [v5MixedPointedFiber_apply, h, v5PointedCancelBaseChange_tmul]
  simp [Algebra.smul_def]


end Fiber
end StrictEUnit
#print axioms StrictEUnit.v5PointedCancelBaseChange
#print axioms StrictEUnit.v5MixedPointedFiber

#print axioms StrictEUnit.v5MixedPointedFiber_of_pure
