import BialgebraBaseChange
import PVConstantHopfAlgebra

/-! Actual base change of the constant-multiplication chart. -/
open scoped TensorProduct
open TensorProduct
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k B A R H : Type*} [CommRing k] [CommRing B] [CommRing A] [CommRing R] [CommRing H]
  [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A]
  [Algebra k R] [Algebra B R] [IsScalarTower k B R] [Algebra k H]

/-- A heterogeneous algebra associator, with no flatness assumption. -/
def fiberMixedAssoc :
    (A ⊗[B] R) ⊗[k] H ≃ₐ[A] A ⊗[B] (R ⊗[k] H) :=
by
  let e : (A ⊗[B] R) ⊗[k] H ≃ₗ[A] A ⊗[B] (R ⊗[k] H) :=
    TensorProduct.AlgebraTensorModule.assoc k B A A R H
  have hz : e (0 : (A ⊗[B] R) ⊗[k] H) = (0 : A ⊗[B] (R ⊗[k] H)) :=
    LinearEquiv.map_zero e
  have ha (x y : (A ⊗[B] R) ⊗[k] H) : e (x + y) = e x + e y :=
    LinearEquiv.map_add e x y
  refine AlgEquiv.ofLinearEquiv e rfl ?_
  intro x y
  induction x using TensorProduct.induction_on with
  | zero => rw [zero_mul, hz, zero_mul]
  | add x y hx hy => simp only [add_mul, ha, hx, hy]
  | tmul x h =>
    induction x using TensorProduct.induction_on with
    | zero => rw [zero_tmul, zero_mul, hz, zero_mul]
    | add x y hx hy => simp only [add_tmul, add_mul, ha, hx, hy]
    | tmul a r =>
      induction y using TensorProduct.induction_on with
      | zero => rw [mul_zero, hz, mul_zero]
      | add x y hx hy => simp only [mul_add, ha, hx, hy]
      | tmul y g =>
        induction y using TensorProduct.induction_on with
        | zero => rw [zero_tmul, mul_zero, hz, mul_zero]
        | add x y hx hy => simp only [add_tmul, mul_add, ha, hx, hy]
        | tmul a' r' =>
          simp only [Algebra.TensorProduct.tmul_mul_tmul, e, AlgebraTensorModule.assoc_tmul]

@[simp] theorem fiberMixedAssoc_tmul (a:A) (r:R) (h:H) :
    fiberMixedAssoc (k:=k) (B:=B) ((a ⊗ₜ[B] r) ⊗ₜ[k] h) =
      a ⊗ₜ[B] (r ⊗ₜ[k] h) := rfl

/-- Base-change the actual multiplication equivalence and distribute tensors. -/
def fiberMultiplicationChartAux (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) :
    (A ⊗[B] R) ⊗[k] H ≃ₐ[A] (A ⊗[B] R) ⊗[A] (A ⊗[B] R) :=
  (fiberMixedAssoc (k:=k) (B:=B)).trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl (R:=A) (A₁:=A))
      (e.restrictScalars B)).trans
        (algebraTensorBaseChangeEquiv (k:=B) A R R).symm)

@[simp] theorem fiberMultiplicationChartAux_tmul
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) (a:A) (r:R) (h:H) :
    fiberMultiplicationChartAux (A:=A) e ((a ⊗ₜ[B] r) ⊗ₜ[k] h) =
      (algebraTensorBaseChangeEquiv (k:=B) A R R).symm (a ⊗ₜ[B] e (r ⊗ₜ[k] h)) := rfl

theorem fiberMultiplicationChartAux_scalar
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) (s:A ⊗[B] R) :
    fiberMultiplicationChartAux (A:=A) e (s ⊗ₜ[k] (1:H)) =
      s ⊗ₜ[A] (1:A ⊗[B] R) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
  | tmul a r =>
    rw [fiberMultiplicationChartAux_tmul]
    have hr : e (r ⊗ₜ[k] (1:H)) = r ⊗ₜ[B] (1:R) := e.commutes r
    rw [hr, algebraTensorBaseChangeEquiv_symm_tmul]
    rfl

/-- The base-changed chart retains its actual left-fiber algebra structure. -/
def fiberMultiplicationChart (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) :
    (A ⊗[B] R) ⊗[k] H ≃ₐ[A ⊗[B] R] (A ⊗[B] R) ⊗[A] (A ⊗[B] R) :=
  { (fiberMultiplicationChartAux (A:=A) e).toRingEquiv with
    commutes' := fiberMultiplicationChartAux_scalar e }

end StrictEUnit
#print axioms StrictEUnit.fiberMixedAssoc
#print axioms StrictEUnit.fiberMixedAssoc_tmul
#print axioms StrictEUnit.fiberMultiplicationChartAux
#print axioms StrictEUnit.fiberMultiplicationChartAux_tmul
#print axioms StrictEUnit.fiberMultiplicationChartAux_scalar
#print axioms StrictEUnit.fiberMultiplicationChart
