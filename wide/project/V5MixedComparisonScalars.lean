import V5MixedComparisonDifferential

open scoped TensorProduct
open TensorProduct

noncomputable section
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1100000
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
namespace StrictEUnit

variable {k B R S : Type*} [Field k] [CommRing B] [CommRing R] [CommRing S]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
  [Algebra k S] [Algebra B S] [IsScalarTower k B S]

/-- Form the comparison directly as a k-algebra map; it has the same
underlying function as comparison by multiplication over R. -/
def v5MixedConstantMultiplicationK
    (d : Derivation k (R ⊗[B] S) (R ⊗[B] S)) :
    R ⊗[k] derivationConstants d →ₐ[k] R ⊗[B] S :=
  (v5MixedConstantMultiplication d).restrictScalars k

@[simp] theorem v5MixedConstantMultiplicationK_apply
    (d : Derivation k (R ⊗[B] S) (R ⊗[B] S))
    (x : R ⊗[k] derivationConstants d) :
    v5MixedConstantMultiplicationK d x = v5MixedConstantMultiplication d x := rfl

def v5MixedComparisonK
    (d : Derivation k (R ⊗[B] S) (R ⊗[B] S))
    (hd : Function.Bijective (v5MixedConstantMultiplication d)) :
    R ⊗[k] derivationConstants d ≃ₐ[k] R ⊗[B] S :=
  AlgEquiv.ofBijective (v5MixedConstantMultiplicationK d) hd

@[simp] theorem v5MixedComparisonK_apply
    (d : Derivation k (R ⊗[B] S) (R ⊗[B] S))
    (hd : Function.Bijective (v5MixedConstantMultiplication d))
    (x : R ⊗[k] derivationConstants d) :
    v5MixedComparisonK d hd x = v5MixedConstantMultiplication d x := rfl

theorem v5MixedComparisonK_differential
    (dB : Derivation k B B) (dR : Derivation k R R) (dS : Derivation k S S)
    (hR : ∀ b, dR (algebraMap B R b) = algebraMap B R (dB b))
    (hS : ∀ b, dS (algebraMap B S b) = algebraMap B S (dB b))
    (hd : Function.Bijective (v5MixedConstantMultiplication (mixedRelativeTensorDerivation dB dR dS hR hS)))
    (x : R ⊗[k] derivationConstants (mixedRelativeTensorDerivation dB dR dS hR hS)) :
    let d := mixedRelativeTensorDerivation dB dR dS hR hS
    d (v5MixedComparisonK d hd x) = v5MixedComparisonK d hd (tensorDerivation dR x) :=
  v5_mixedConstantMultiplication_differential dB dR dS hR hS x

end StrictEUnit
#print axioms StrictEUnit.v5MixedConstantMultiplicationK
#print axioms StrictEUnit.v5MixedConstantMultiplicationK_apply
#print axioms StrictEUnit.v5MixedComparisonK
#print axioms StrictEUnit.v5MixedComparisonK_apply
#print axioms StrictEUnit.v5MixedComparisonK_differential
