import Mathlib.RingTheory.TensorProduct.Basic
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
variable {K R U : Type*} [CommRing K] [CommRing R] [CommRing U]
  [Algebra K R] [Algebra K U]
def v5TargetRing129 (H : Subalgebra K U) : CommRing (R ⊗[K] H) := inferInstance
def v5TargetAlgebra129 (H : Subalgebra K U) : Algebra R (R ⊗[K] H) :=
  Algebra.TensorProduct.leftAlgebra
end StrictEUnit
#print axioms StrictEUnit.v5TargetRing129
#print axioms StrictEUnit.v5TargetAlgebra129
