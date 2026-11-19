import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.TensorProduct.Basic
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
variable {B R : Type*} [CommRing B] [CommRing R] [Algebra B R]

def V5SubalgebraSource128 (T : Subalgebra B R) := R ⊗[B] T
instance v5SubalgebraSourceRing128 (T : Subalgebra B R) : CommRing (V5SubalgebraSource128 T) :=
  inferInstanceAs (CommRing (R ⊗[B] T))
instance v5SubalgebraSourceAlgebra128 (T : Subalgebra B R) : Algebra R (V5SubalgebraSource128 T) :=
  inferInstanceAs (Algebra R (R ⊗[B] T))

def v5SubalgebraSourceInclusion128 (T : Subalgebra B R) :
    V5SubalgebraSource128 T →ₗ[R] R ⊗[B] R :=
  TensorProduct.AlgebraTensorModule.lTensor R R T.val.toLinearMap

theorem v5SubalgebraSourceInclusion128_injective [Module.Flat B R] (T : Subalgebra B R) :
    Function.Injective (v5SubalgebraSourceInclusion128 T) :=
  Module.Flat.lTensor_preserves_injective_linearMap T.val.toLinearMap
    (fun _ _ h => Subtype.ext h)
end StrictEUnit
#print axioms StrictEUnit.v5SubalgebraSourceRing128
#print axioms StrictEUnit.v5SubalgebraSourceAlgebra128
#print axioms StrictEUnit.v5SubalgebraSourceInclusion128
#print axioms StrictEUnit.v5SubalgebraSourceInclusion128_injective
