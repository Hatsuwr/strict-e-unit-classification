import WeightSpaces
import Mathlib.RingTheory.Derivation.Basic

/-! Extension of a derivation to a tensor product, holding the second
factor constant. No differential compatibility of a coaction is assumed
or constructed by this definition. -/
open scoped TensorProduct
open TensorProduct
noncomputable section
namespace StrictEUnit
variable {k R H : Type*} [CommRing k] [CommRing R] [CommRing H]
  [Algebra k R] [Algebra k H]

/-- The actual linear operator δ tensor identity. -/
def tensorDerivationLinear (δ : Derivation k R R) : R ⊗[k] H →ₗ[k] R ⊗[k] H :=
  δ.toLinearMap.rTensor H

@[simp] theorem tensorDerivationLinear_tmul (δ : Derivation k R R) (r : R) (h : H) :
    tensorDerivationLinear δ (r ⊗ₜ[k] h) = δ r ⊗ₜ[k] h := rfl

theorem tensorDerivationLinear_mul (δ : Derivation k R R) (x y : R ⊗[k] H) :
    tensorDerivationLinear δ (x*y) =
      x * tensorDerivationLinear δ y + y * tensorDerivationLinear δ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r h =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul s j =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, tensorDerivationLinear_tmul,
        Derivation.leibniz, smul_eq_mul, add_tmul]
      congr 1
      rw [mul_comm h j]
    | add y z hy hz => simp only [mul_add, map_add, add_mul, hy, hz]; abel
  | add x z hx hz => simp only [add_mul, map_add, mul_add, hx, hz]; abel

/-- A genuine derivation, with Leibniz proved on all tensors. -/
def tensorDerivation (δ : Derivation k R R) : Derivation k (R ⊗[k] H) (R ⊗[k] H) :=
  Derivation.mk' (tensorDerivationLinear δ) (tensorDerivationLinear_mul δ)

@[simp] theorem tensorDerivation_tmul (δ : Derivation k R R) (r : R) (h : H) :
    tensorDerivation δ (r ⊗ₜ[k] h) = δ r ⊗ₜ[k] h := rfl
end StrictEUnit

#print axioms StrictEUnit.tensorDerivationLinear
#print axioms StrictEUnit.tensorDerivationLinear_tmul
#print axioms StrictEUnit.tensorDerivationLinear_mul
#print axioms StrictEUnit.tensorDerivation
#print axioms StrictEUnit.tensorDerivation_tmul
