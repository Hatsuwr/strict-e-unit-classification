import PairingBaseChange
import Mathlib.RingTheory.Bialgebra.Basic

/-! Actual algebra maps for scalar extension of a bialgebra. The cover
algebra carries no bialgebra structure. Coalgebra laws are separate proofs. -/
open scoped TensorProduct
open TensorProduct
noncomputable section
set_option maxHeartbeats 200000
namespace StrictEUnit
attribute [local instance 2000] Algebra.toModule
set_option synthInstance.maxHeartbeats 20000
section Tensor
variable {k : Type*} [CommRing k]
variable (A M N : Type*) [CommRing A] [CommRing M] [CommRing N]
  [Algebra k A] [Algebra k M] [Algebra k N]

/-- Algebraic distribution of tensor products after scalar extension. -/
def algebraTensorBaseChangeEquiv :
    (A ⊗[k] M) ⊗[A] (A ⊗[k] N) ≃ₐ[A] A ⊗[k] (M ⊗[k] N) := by
  letI : CommRing (A ⊗[A] A) := Algebra.TensorProduct.instCommRing
  letI : Algebra k (A ⊗[A] A) := Algebra.TensorProduct.leftAlgebra
  letI : CommRing ((A ⊗[A] A) ⊗[k] (M ⊗[k] N)) := Algebra.TensorProduct.instCommRing
  exact (Algebra.TensorProduct.tensorTensorTensorComm k A A M A N).trans
    (Algebra.TensorProduct.congr (Algebra.TensorProduct.lid A A)
      (AlgEquiv.refl (R := k) (A₁ := M ⊗[k] N)))

@[simp] theorem algebraTensorBaseChangeEquiv_tmul
    (a b : A) (m : M) (n : N) :
    algebraTensorBaseChangeEquiv (k := k) A M N
      ((a ⊗ₜ[k] m) ⊗ₜ[A] (b ⊗ₜ[k] n)) = (a * b) ⊗ₜ[k] (m ⊗ₜ[k] n) := by
  change (a * b) ⊗ₜ[k] (m ⊗ₜ[k] n) = (a * b) ⊗ₜ[k] (m ⊗ₜ[k] n)
  rfl

@[simp] theorem algebraTensorBaseChangeEquiv_symm_tmul
    (a : A) (m : M) (n : N) :
    (algebraTensorBaseChangeEquiv (k := k) A M N).symm (a ⊗ₜ[k] (m ⊗ₜ[k] n)) =
      (a ⊗ₜ[k] m) ⊗ₜ[A] ((1 : A) ⊗ₜ[k] n) := by
  apply (algebraTensorBaseChangeEquiv (k := k) A M N).injective
  simp only [AlgEquiv.apply_symm_apply, algebraTensorBaseChangeEquiv_tmul, mul_one]
end Tensor

section Bialgebra
variable {k H : Type*} [CommRing k] [CommRing H] [Bialgebra k H]
variable (A : Type*) [CommRing A] [Algebra k A]

/-- The actual scalar-extended comultiplication. -/
def baseChangeComul :
    A ⊗[k] H →ₐ[A] (A ⊗[k] H) ⊗[A] (A ⊗[k] H) :=
  (algebraTensorBaseChangeEquiv (k := k) A H H).symm.toAlgHom.comp
    (weightBaseChangeAlgHom A (Bialgebra.comulAlgHom k H))

/-- The actual scalar-extended counit. -/
def baseChangeCounit : A ⊗[k] H →ₐ[A] A :=
  (Algebra.TensorProduct.rid k A A).toAlgHom.comp
    (weightBaseChangeAlgHom A (Bialgebra.counitAlgHom k H))

@[simp] theorem baseChangeComul_tmul (a : A) (h : H) :
    baseChangeComul A (a ⊗ₜ[k] h) =
      (algebraTensorBaseChangeEquiv (k := k) A H H).symm
        (a ⊗ₜ[k] Coalgebra.comul (R := k) h) := rfl

@[simp] theorem baseChangeCounit_tmul (a : A) (h : H) :
    baseChangeCounit A (a ⊗ₜ[k] h) =
      a * algebraMap k A (Coalgebra.counit (R := k) h) := by
  change Coalgebra.counit (R := k) h • a = _
  rw [Algebra.smul_def, mul_comm]

end Bialgebra
end StrictEUnit

#print axioms StrictEUnit.algebraTensorBaseChangeEquiv
#print axioms StrictEUnit.algebraTensorBaseChangeEquiv_tmul
#print axioms StrictEUnit.algebraTensorBaseChangeEquiv_symm_tmul
#print axioms StrictEUnit.baseChangeComul
#print axioms StrictEUnit.baseChangeCounit
#print axioms StrictEUnit.baseChangeComul_tmul
#print axioms StrictEUnit.baseChangeCounit_tmul
