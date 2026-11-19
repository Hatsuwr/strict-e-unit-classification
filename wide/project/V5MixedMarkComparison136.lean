import V5MixedComparisonScalars
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k B R S : Type*} [Field k] [CommRing B] [CommRing R] [CommRing S]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
  [Algebra k S] [Algebra B S] [IsScalarTower k B S]
theorem v5MixedConstantMultiplication_constant136
    (d : Derivation k (R ⊗[B] S) (R ⊗[B] S)) (c : derivationConstants d) :
    v5MixedConstantMultiplication d ((1 : R) ⊗ₜ[k] c) = c.val := by
  change algebraMap R (R ⊗[B] S) (1 : R) * c.val = c.val
  rw [map_one, one_mul]
theorem v5MixedComparisonK_constant136
    (d : Derivation k (R ⊗[B] S) (R ⊗[B] S))
    (hd : Function.Bijective (v5MixedConstantMultiplication d))
    (c : derivationConstants d) :
    v5MixedComparisonK d hd ((1 : R) ⊗ₜ[k] c) = c.val :=
  v5MixedConstantMultiplication_constant136 d c
end StrictEUnit
#print axioms StrictEUnit.v5MixedConstantMultiplication_constant136
#print axioms StrictEUnit.v5MixedComparisonK_constant136
