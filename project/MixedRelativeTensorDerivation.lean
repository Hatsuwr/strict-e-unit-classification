import RelativeTensorDerivation
import Mathlib.RingTheory.Flat.Basic

/-! Mixed relative tensor differentiation and its actual functorial left
factor map. Flatness is explicit in the injectivity theorem, not derived. -/
open scoped TensorProduct
open TensorProduct
noncomputable section
namespace StrictEUnit
variable {k B E R : Type*} [CommRing k] [CommRing B] [CommRing E] [CommRing R]
  [Algebra k B] [Algebra k E] [Algebra B E] [IsScalarTower k B E]
  [Algebra k R] [Algebra B R] [IsScalarTower k B R]

def mixedTensorBilinear (dE : Derivation k E E) (dR : Derivation k R R) :
    E →+ R →+ E ⊗[B] R where
  toFun e :=
    { toFun := fun r => dE e ⊗ₜ[B] r + e ⊗ₜ[B] dR r
      map_zero' := by simp
      map_add' := by intro r s; simp only [tmul_add, map_add]; abel }
  map_zero' := by ext r; simp
  map_add' e f := by
    ext r
    change dE (e+f) ⊗ₜ[B] r + (e+f) ⊗ₜ[B] dR r =
      (dE e ⊗ₜ[B] r + e ⊗ₜ[B] dR r) + (dE f ⊗ₜ[B] r + f ⊗ₜ[B] dR r)
    simp only [map_add, add_tmul]
    abel

theorem mixedTensorBilinear_balanced
    (dB : Derivation k B B) (dE : Derivation k E E) (dR : Derivation k R R)
    (hE : ∀ b, dE (algebraMap B E b) = algebraMap B E (dB b))
    (hR : ∀ b, dR (algebraMap B R b) = algebraMap B R (dB b))
    (b : B) (e : E) (r : R) :
    mixedTensorBilinear (B := B) dE dR (b • e) r = mixedTensorBilinear (B := B) dE dR e (b • r) := by
  change dE (b • e) ⊗ₜ[B] r + (b • e) ⊗ₜ[B] dR r =
    dE e ⊗ₜ[B] (b • r) + e ⊗ₜ[B] dR (b • r)
  rw [differential_algebra_smul dB dE hE, differential_algebra_smul dB dR hR]
  simp only [add_tmul, tmul_add, smul_tmul]
  abel

def mixedRelativeDerivativeAdd
    (dB : Derivation k B B) (dE : Derivation k E E) (dR : Derivation k R R)
    (hE : ∀ b, dE (algebraMap B E b) = algebraMap B E (dB b))
    (hR : ∀ b, dR (algebraMap B R b) = algebraMap B R (dB b)) :
    E ⊗[B] R →+ E ⊗[B] R :=
  TensorProduct.liftAddHom (mixedTensorBilinear (B := B) dE dR)
    (mixedTensorBilinear_balanced dB dE dR hE hR)

@[simp] theorem mixedRelativeDerivativeAdd_tmul
    (dB : Derivation k B B) (dE : Derivation k E E) (dR : Derivation k R R)
    (hE : ∀ b, dE (algebraMap B E b) = algebraMap B E (dB b))
    (hR : ∀ b, dR (algebraMap B R b) = algebraMap B R (dB b)) (e : E) (r : R) :
    mixedRelativeDerivativeAdd dB dE dR hE hR (e ⊗ₜ[B] r) =
      dE e ⊗ₜ[B] r + e ⊗ₜ[B] dR r := rfl

def mixedRelativeDerivativeLinear
    (dB : Derivation k B B) (dE : Derivation k E E) (dR : Derivation k R R)
    (hE : ∀ b, dE (algebraMap B E b) = algebraMap B E (dB b))
    (hR : ∀ b, dR (algebraMap B R b) = algebraMap B R (dB b)) :
    E ⊗[B] R →ₗ[k] E ⊗[B] R :=
  { mixedRelativeDerivativeAdd dB dE dR hE hR with
    map_smul' := by
      intro a x
      change mixedRelativeDerivativeAdd dB dE dR hE hR (a • x) =
        a • mixedRelativeDerivativeAdd dB dE dR hE hR x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul e r =>
        simp only [smul_tmul', mixedRelativeDerivativeAdd_tmul,
          Derivation.map_smul, smul_add]
      | add x y hx hy => simp only [smul_add, map_add, hx, hy] }

@[simp] theorem mixedRelativeDerivativeLinear_tmul
    (dB : Derivation k B B) (dE : Derivation k E E) (dR : Derivation k R R)
    (hE : ∀ b, dE (algebraMap B E b) = algebraMap B E (dB b))
    (hR : ∀ b, dR (algebraMap B R b) = algebraMap B R (dB b)) (e : E) (r : R) :
    mixedRelativeDerivativeLinear dB dE dR hE hR (e ⊗ₜ[B] r) =
      dE e ⊗ₜ[B] r + e ⊗ₜ[B] dR r := rfl

theorem mixedRelativeDerivativeLinear_mul
    (dB : Derivation k B B) (dE : Derivation k E E) (dR : Derivation k R R)
    (hE : ∀ b, dE (algebraMap B E b) = algebraMap B E (dB b))
    (hR : ∀ b, dR (algebraMap B R b) = algebraMap B R (dB b)) (x y : E ⊗[B] R) :
    mixedRelativeDerivativeLinear dB dE dR hE hR (x*y) =
      x * mixedRelativeDerivativeLinear dB dE dR hE hR y +
      y * mixedRelativeDerivativeLinear dB dE dR hE hR x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul e r =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul f s =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mixedRelativeDerivativeLinear_tmul,
        Derivation.leibniz, smul_eq_mul, add_tmul, tmul_add, mul_add,
        Algebra.TensorProduct.tmul_mul_tmul]
      simp only [mul_comm]
      abel
    | add y z hy hz => simp only [mul_add, map_add, add_mul, hy, hz]; abel
  | add x z hx hz => simp only [add_mul, map_add, mul_add, hx, hz]; abel

def mixedRelativeTensorDerivation
    (dB : Derivation k B B) (dE : Derivation k E E) (dR : Derivation k R R)
    (hE : ∀ b, dE (algebraMap B E b) = algebraMap B E (dB b))
    (hR : ∀ b, dR (algebraMap B R b) = algebraMap B R (dB b)) :
    Derivation k (E ⊗[B] R) (E ⊗[B] R) :=
  Derivation.mk' (mixedRelativeDerivativeLinear dB dE dR hE hR)
    (mixedRelativeDerivativeLinear_mul dB dE dR hE hR)

@[simp] theorem mixedRelativeTensorDerivation_tmul
    (dB : Derivation k B B) (dE : Derivation k E E) (dR : Derivation k R R)
    (hE : ∀ b, dE (algebraMap B E b) = algebraMap B E (dB b))
    (hR : ∀ b, dR (algebraMap B R b) = algebraMap B R (dB b)) (e : E) (r : R) :
    mixedRelativeTensorDerivation dB dE dR hE hR (e ⊗ₜ[B] r) =
      dE e ⊗ₜ[B] r + e ⊗ₜ[B] dR r := rfl

theorem mixedRelativeTensorDerivation_map_left
    (dB : Derivation k B B) (dE : Derivation k E E) (dR : Derivation k R R)
    (hE : ∀ b, dE (algebraMap B E b) = algebraMap B E (dB b))
    (hR : ∀ b, dR (algebraMap B R b) = algebraMap B R (dB b))
    (f : R →ₐ[B] E) (hf : ∀ r, dE (f r) = f (dR r)) (z : R ⊗[B] R) :
    mixedRelativeTensorDerivation dB dE dR hE hR
      (Algebra.TensorProduct.map f (AlgHom.id B R) z) =
    Algebra.TensorProduct.map f (AlgHom.id B R)
      (relativeTensorDerivation dB dR hR z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r s =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      mixedRelativeTensorDerivation_tmul, relativeTensorDerivation_tmul, map_add, hf]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem relativeTensorMap_left_injective [Module.Flat B R]
    (f : R →ₐ[B] E) (hf : Function.Injective f) :
    Function.Injective (Algebra.TensorProduct.map f (AlgHom.id B R)) := by
  exact Module.Flat.rTensor_preserves_injective_linearMap f.toLinearMap hf
end StrictEUnit

#print axioms StrictEUnit.mixedTensorBilinear
#print axioms StrictEUnit.mixedTensorBilinear_balanced
#print axioms StrictEUnit.mixedRelativeDerivativeAdd
#print axioms StrictEUnit.mixedRelativeDerivativeAdd_tmul
#print axioms StrictEUnit.mixedRelativeDerivativeLinear
#print axioms StrictEUnit.mixedRelativeDerivativeLinear_tmul
#print axioms StrictEUnit.mixedRelativeDerivativeLinear_mul
#print axioms StrictEUnit.mixedRelativeTensorDerivation
#print axioms StrictEUnit.mixedRelativeTensorDerivation_tmul
#print axioms StrictEUnit.mixedRelativeTensorDerivation_map_left
#print axioms StrictEUnit.relativeTensorMap_left_injective
