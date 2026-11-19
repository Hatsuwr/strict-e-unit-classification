import Mathlib.Algebra.Algebra.Equiv

/-! Fixed-bundle identities avoid morphism-class search on deeply nested
specialized tensor charts. These are the existing structure laws. -/
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit.TypedMaps
variable {S A C : Type*}
  [CommSemiring S] [Semiring A] [Semiring C]
  [Algebra S A] [Algebra S C]

theorem algEquiv_zero (f : A ≃ₐ[S] C) : f (0 : A) = (0 : C) :=
  RingEquiv.map_zero f.toRingEquiv

theorem algEquiv_add (f : A ≃ₐ[S] C) (x y : A) :
    f (x + y) = f x + f y := f.map_add' x y

theorem algEquiv_mul (f : A ≃ₐ[S] C) (x y : A) :
    f (x * y) = f x * f y := f.map_mul' x y

theorem algHom_zero (f : A →ₐ[S] C) : f (0 : A) = (0 : C) := f.map_zero'

theorem algHom_add (f : A →ₐ[S] C) (x y : A) :
    f (x + y) = f x + f y := f.map_add' x y

theorem algHom_mul (f : A →ₐ[S] C) (x y : A) :
    f (x * y) = f x * f y := f.map_mul' x y

end StrictEUnit.TypedMaps
