import PVConstantAlgebra
noncomputable section
namespace StrictEUnit
variable {k M : Type*} [CommRing k] [CommRing M] [Algebra k M]
def v5DerivationConstantsInclusion136 (d : Derivation k M M) : derivationConstants d →ₐ[k] M :=
  (derivationConstants d).val
end StrictEUnit
#print axioms StrictEUnit.v5DerivationConstantsInclusion136

open scoped TensorProduct
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k B R S : Type*} [CommRing k] [CommRing B] [CommRing R] [CommRing S]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
  [Algebra k S] [Algebra B S] [IsScalarTower k B S]
def v5MixedConstantsMarkInclusion136
    (d : Derivation k (R ⊗[B] S) (R ⊗[B] S)) :
    derivationConstants d →ₐ[k] R ⊗[B] S := (derivationConstants d).val
end StrictEUnit
#print axioms StrictEUnit.v5MixedConstantsMarkInclusion136
