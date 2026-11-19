import TorsorChartTarget
import MixedRelativeTensorDerivation
import TensorConstants

/-! Actual mixed-base algebra reassociation and the triple chart. -/
open scoped TensorProduct
open TensorProduct
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k B R H : Type*} [CommRing k] [CommRing B] [CommRing R] [CommRing H]
  [Algebra k B] [Algebra k R] [Algebra k H] [Algebra B R] [IsScalarTower k B R]

/-- Upgrade the genuine mixed-base linear associator by proving multiplicativity. -/
def mixedAlgebraAssoc :
    (R ⊗[B] R) ⊗[k] H ≃ₐ[R] R ⊗[B] (R ⊗[k] H) :=
by
  let e : (R ⊗[B] R) ⊗[k] H ≃ₗ[R] R ⊗[B] (R ⊗[k] H) :=
    TensorProduct.AlgebraTensorModule.assoc k B R R R H
  have hz : e (0 : (R ⊗[B] R) ⊗[k] H) = (0 : R ⊗[B] (R ⊗[k] H)) := e.map_zero
  have ha (x y : (R ⊗[B] R) ⊗[k] H) : e (x + y) = e x + e y := e.map_add x y
  refine AlgEquiv.ofLinearEquiv e rfl ?_
  intro x y
  induction x using TensorProduct.induction_on with
  | zero => rw [zero_mul, hz, zero_mul]
  | add x y hx hy => simp only [add_mul, ha, hx, hy]
  | tmul x h =>
    induction x using TensorProduct.induction_on with
    | zero => rw [zero_tmul, zero_mul, hz, zero_mul]
    | add x y hx hy => simp only [add_tmul, add_mul, ha, hx, hy]
    | tmul r s =>
      induction y using TensorProduct.induction_on with
      | zero => rw [mul_zero, hz, mul_zero]
      | add x y hx hy => simp only [mul_add, ha, hx, hy]
      | tmul y h' =>
        induction y using TensorProduct.induction_on with
        | zero => rw [zero_tmul, mul_zero, hz, mul_zero]
        | add x y hx hy => simp only [add_tmul, mul_add, ha, hx, hy]
        | tmul r' s' =>
          simp only [Algebra.TensorProduct.tmul_mul_tmul, e, AlgebraTensorModule.assoc_tmul]

@[simp] theorem mixedAlgebraAssoc_tmul (r s : R) (h : H) :
    mixedAlgebraAssoc (k:=k) (B:=B) ((r ⊗ₜ[B] s) ⊗ₜ[k] h) =
      r ⊗ₜ[B] (s ⊗ₜ[k] h) := rfl

/-- The actual triple chart, using the same multiplication chart twice. -/
def pvTripleChart (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) :
    R ⊗[k] (H ⊗[k] H) ≃ₐ[R] R ⊗[B] (R ⊗[B] R) :=
  (leftAlgebraAssoc (B:=k) (R:=R) H H).symm |>.trans
    ((Algebra.TensorProduct.congr e (AlgEquiv.refl (R:=k) (A₁:=H))).trans
      ((mixedAlgebraAssoc (k:=k) (B:=B)).trans
        (Algebra.TensorProduct.congr (AlgEquiv.refl (R:=R) (A₁:=R))
          (e.restrictScalars B))))

@[simp] theorem pvTripleChart_tmul
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) (r : R) (h g : H) :
    pvTripleChart e (r ⊗ₜ[k] (h ⊗ₜ[k] g)) =
      Algebra.TensorProduct.map (AlgHom.id B R) (e.toAlgHom.restrictScalars B)
        (mixedAlgebraAssoc (k:=k) (B:=B) (e (r ⊗ₜ[k] h) ⊗ₜ[k] g)) := rfl

end StrictEUnit
#print axioms StrictEUnit.mixedAlgebraAssoc
#print axioms StrictEUnit.mixedAlgebraAssoc_tmul
#print axioms StrictEUnit.pvTripleChart

#print axioms StrictEUnit.pvTripleChart_tmul
