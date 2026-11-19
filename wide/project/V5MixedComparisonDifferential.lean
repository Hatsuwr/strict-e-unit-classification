import V5MixedComparisonSurjectivity

open scoped TensorProduct
open TensorProduct

noncomputable section
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
namespace StrictEUnit

variable {k B R S : Type*} [Field k] [CommRing B] [CommRing R] [CommRing S]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
  [Algebra k S] [Algebra B S] [IsScalarTower k B S]

/-- The multiplication map defining the mixed comparison is differential. -/
theorem v5_mixedConstantMultiplication_differential
    (dB : Derivation k B B) (dR : Derivation k R R) (dS : Derivation k S S)
    (hR : ∀ b, dR (algebraMap B R b) = algebraMap B R (dB b))
    (hS : ∀ b, dS (algebraMap B S b) = algebraMap B S (dB b))
    (x : R ⊗[k] derivationConstants (mixedRelativeTensorDerivation dB dR dS hR hS)) :
    let d := mixedRelativeTensorDerivation dB dR dS hR hS
    d (v5MixedConstantMultiplication d x) =
      v5MixedConstantMultiplication d (tensorDerivation dR x) := by
  let d := mixedRelativeTensorDerivation dB dR dS hR hS
  change d (v5MixedConstantMultiplication d x) =
      v5MixedConstantMultiplication d (tensorDerivation dR x)
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r c =>
    rw [tensorDerivation_tmul]
    change d ((r ⊗ₜ[B] (1 : S)) * c.val) = (dR r ⊗ₜ[B] (1 : S)) * c.val
    rw [Derivation.leibniz, c.property, smul_zero, zero_add, smul_eq_mul]
    rw [show d (r ⊗ₜ[B] (1 : S)) = _ from mixedRelativeTensorDerivation_tmul dB dR dS hR hS r 1]
    simp [mul_comm]

end StrictEUnit
#print axioms StrictEUnit.v5_mixedConstantMultiplication_differential
