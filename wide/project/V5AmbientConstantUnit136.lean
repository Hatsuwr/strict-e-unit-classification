import V5MixedConstantsDescent
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k B R S : Type*} [Field k] [CommRing B] [CommRing R] [CommRing S]
  [Algebra k B] [Algebra k R] [Algebra k S] [Algebra B R] [Algebra B S]
  [IsScalarTower k B R] [IsScalarTower k B S]
def v5AmbientConstantUnit136
    (d : Derivation k (R ⊗[B] S) (R ⊗[B] S)) (u : (derivationConstants d)ˣ) :
    (R ⊗[B] S)ˣ :=
  Units.map (derivationConstants d).val.toMonoidHom u
theorem v5AmbientConstantUnit_horizontal136
    (d : Derivation k (R ⊗[B] S) (R ⊗[B] S)) (u : (derivationConstants d)ˣ) :
    d (v5AmbientConstantUnit136 d u : R ⊗[B] S) = 0 :=
  u.val.property
end StrictEUnit
#print axioms StrictEUnit.v5AmbientConstantUnit136

#print axioms StrictEUnit.v5AmbientConstantUnit_horizontal136
