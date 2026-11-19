import Mathlib.RingTheory.TensorProduct.Basic
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
def v5SelfTensorAlgebra129 (B R : Type*) [CommRing B] [CommRing R] [Algebra B R] :
    Algebra R (R ⊗[B] R) := Algebra.TensorProduct.leftAlgebra
end StrictEUnit
#print axioms StrictEUnit.v5SelfTensorAlgebra129
