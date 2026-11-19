import MixedRelativeTensorDerivation
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
set_option maxHeartbeats 600000
set_option maxRecDepth 1600
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k B R W : Type*}
  [CommRing k] [CommRing B] [CommRing R] [CommRing W]
  [Algebra k B] [Algebra k R] [Algebra k W] [Algebra B R] [Algebra B W]
  [IsScalarTower k B R] [IsScalarTower k B W]

/-- Pointwise scaling on both tensor factors gives the same scalar multiple
of the mixed derivation. The coefficient is allowed to vary in B. -/
theorem v5MixedDerivationScale136
    (dB0 : Derivation k B B) (dR0 : Derivation k R R) (dW0 : Derivation k W W)
    (hR0 : ∀ b, dR0 (algebraMap B R b) = algebraMap B R (dB0 b))
    (hW0 : ∀ b, dW0 (algebraMap B W b) = algebraMap B W (dB0 b))
    (c : B) (dR1 : R → R) (dW1 : W → W)
    (dOld1 : Derivation k (R ⊗[B] W) (R ⊗[B] W))
    (hR1 : ∀ r, dR1 r = algebraMap B R c * dR0 r)
    (hW1 : ∀ w, dW1 w = algebraMap B W c * dW0 w)
    (hOld1 : ∀ r w, dOld1 (r ⊗ₜ[B] w) = dR1 r ⊗ₜ[B] w + r ⊗ₜ[B] dW1 w)
    (z : R ⊗[B] W) :
    dOld1 z = algebraMap B (R ⊗[B] W) c *
      mixedRelativeTensorDerivation dB0 dR0 dW0 hR0 hW0 z := by
  let dOld0 := mixedRelativeTensorDerivation dB0 dR0 dW0 hR0 hW0
  change dOld1 z = algebraMap B (R ⊗[B] W) c * dOld0 z
  induction z using TensorProduct.induction_on with
  | zero =>
    have h0 : dOld0 0 = 0 := dOld0.toLinearMap.map_zero
    have h1 : dOld1 0 = 0 := dOld1.toLinearMap.map_zero
    rw [h0, h1, mul_zero]
  | add x y hx hy =>
    have h0 : dOld0 (x + y) = dOld0 x + dOld0 y := dOld0.toLinearMap.map_add' _ _
    have h1 : dOld1 (x + y) = dOld1 x + dOld1 y := dOld1.toLinearMap.map_add' _ _
    rw [h0, h1, hx, hy, mul_add]
  | tmul r w =>
    rw [hOld1, hR1, hW1]
    change (algebraMap B R c * dR0 r) ⊗ₜ[B] w +
      r ⊗ₜ[B] (algebraMap B W c * dW0 w) =
      algebraMap B (R ⊗[B] W) c * (dR0 r ⊗ₜ[B] w + r ⊗ₜ[B] dW0 w)
    simp only [← Algebra.smul_def, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_add]

/-- Original horizontal elements stay horizontal for the genuinely scaled
mixed derivation. No constancy of the coefficient is needed. -/
theorem v5MixedDerivationScaleHorizontal136
    (dB0 : Derivation k B B) (dR0 : Derivation k R R) (dW0 : Derivation k W W)
    (hR0 : ∀ b, dR0 (algebraMap B R b) = algebraMap B R (dB0 b))
    (hW0 : ∀ b, dW0 (algebraMap B W b) = algebraMap B W (dB0 b))
    (c : B) (dR1 : R → R) (dW1 : W → W)
    (dOld1 : Derivation k (R ⊗[B] W) (R ⊗[B] W))
    (hR1 : ∀ r, dR1 r = algebraMap B R c * dR0 r)
    (hW1 : ∀ w, dW1 w = algebraMap B W c * dW0 w)
    (hOld1 : ∀ r w, dOld1 (r ⊗ₜ[B] w) = dR1 r ⊗ₜ[B] w + r ⊗ₜ[B] dW1 w)
    (z : R ⊗[B] W)
    (hz : mixedRelativeTensorDerivation dB0 dR0 dW0 hR0 hW0 z = 0) :
    dOld1 z = 0 := by
  rw [v5MixedDerivationScale136 dB0 dR0 dW0 hR0 hW0 c dR1 dW1 dOld1 hR1 hW1 hOld1, hz, mul_zero]
end StrictEUnit
#print axioms StrictEUnit.v5MixedDerivationScale136
#print axioms StrictEUnit.v5MixedDerivationScaleHorizontal136
