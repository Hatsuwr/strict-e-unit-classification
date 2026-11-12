import PVAntipodeLaws
import Mathlib.RingTheory.HopfAlgebra.Basic

/-! The genuine Hopf algebra of diagonal constants. The antipode is the
actual tensor flip, with both convolution identities proved. -/
open scoped TensorProduct
open TensorProduct
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k B R : Type*} [Field k] [CommRing B] [CommRing R] [Nontrivial R]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
variable (dB : Derivation k B B) (d : Derivation k R R)
  (hb : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
  (he : Function.Bijective (pvConstantMultiplication dB d hb))
  (hc : ∀ r, d r = 0 → ∃ c:k, algebraMap k R c = r)
local notation "H" => pvConstantAlgebra dB d hb
local notation "Δ" => pvConstantComultiplication dB d hb he hc
local notation "ε" => candidateCounit dB d hb hc
local notation "S" => pvConstantFlip dB d hb

theorem pvAntipodeContractionLeft_linear (z:H ⊗[k] H) :
    LinearMap.mul' k H ((S).toLinearMap.rTensor H z) =
      pvAntipodeContractionLeft dB d hb z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul h g => rfl

theorem pvAntipodeContractionRight_linear (z:H ⊗[k] H) :
    LinearMap.mul' k H ((S).toLinearMap.lTensor H z) =
      pvAntipodeContractionRight dB d hb z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul h g => rfl

/-- A named actual Hopf structure; no antipode or coalgebra law is an input. -/
def pvConstantHopfAlgebra : HopfAlgebra k H where
  toBialgebra := pvConstantBialgebra dB d hb he hc
  antipode := (S).toLinearMap
  mul_antipode_rTensor_comul := by
    apply LinearMap.ext
    intro h
    change LinearMap.mul' k H ((S).toLinearMap.rTensor H (Δ h)) = algebraMap k H (ε h)
    rw [pvAntipodeContractionLeft_linear, pvAntipode_left]
  mul_antipode_lTensor_comul := by
    apply LinearMap.ext
    intro h
    change LinearMap.mul' k H ((S).toLinearMap.lTensor H (Δ h)) = algebraMap k H (ε h)
    rw [pvAntipodeContractionRight_linear, pvAntipode_right]

end StrictEUnit
#print axioms StrictEUnit.pvAntipodeContractionLeft_linear
#print axioms StrictEUnit.pvAntipodeContractionRight_linear
#print axioms StrictEUnit.pvConstantHopfAlgebra
