import PVFourfoldChart

/-! Explicit additive and injectivity interface for the fourfold chart,
avoiding nested tensor instance search at specialized constant subalgebras. -/
open scoped TensorProduct
noncomputable section
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
variable {k B R H : Type*} [CommRing k] [CommRing B] [CommRing R] [CommRing H]
  [Algebra k B] [Algebra k R] [Algebra k H] [Algebra B R] [IsScalarTower k B R]

theorem pvFourfoldChart_zero (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) :
    pvFourfoldChart e 0 = 0 := (pvFourfoldChart e).map_zero

theorem pvFourfoldChart_add (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R)
    (x y : R ⊗[k] (H ⊗[k] (H ⊗[k] H))) :
    pvFourfoldChart e (x+y) = pvFourfoldChart e x + pvFourfoldChart e y :=
  (pvFourfoldChart e).map_add x y

theorem pvFourfoldChart_injective (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) :
    Function.Injective (pvFourfoldChart e) := (pvFourfoldChart e).injective
end StrictEUnit
#print axioms StrictEUnit.pvFourfoldChart_zero
#print axioms StrictEUnit.pvFourfoldChart_add
#print axioms StrictEUnit.pvFourfoldChart_injective
