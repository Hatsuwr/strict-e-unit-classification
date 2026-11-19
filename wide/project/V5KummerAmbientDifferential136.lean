import V5KummerAmbientMap136
import MixedRelativeTensorDerivation
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false
set_option maxRecDepth 1600
set_option synthInstance.maxHeartbeats 20000
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
local instance algebraSMulCommAmbientDiff136 (A B C : Type*) [CommRing A] [CommRing B]
    [CommRing C] [Algebra A C] [Algebra B C] : SMulCommClass A B C :=
  ⟨fun a b c => by simp only [Algebra.smul_def]; exact mul_left_comm _ _ _⟩
variable {k B T L R W N : Type*}
  [CommRing k] [CommRing B] [CommRing T] [CommRing L] [CommRing R]
  [CommRing W] [CommRing N]
  [Algebra k B] [Algebra k T] [Algebra k L] [Algebra k R] [Algebra k W] [Algebra k N]
  [Algebra B T] [Algebra B L] [Algebra B R] [Algebra B W]
  [Algebra T L] [Algebra T R]
  [IsScalarTower k B T] [IsScalarTower k B L] [IsScalarTower k B R] [IsScalarTower k B W]
  [IsScalarTower k T L] [IsScalarTower k T R]
  [IsScalarTower B T L] [IsScalarTower B T R]

theorem v5DerivationTowerCompatible136
    (dB : Derivation k B B) (dT : Derivation k T T) (dL : Derivation k L L)
    (hT : ∀ b, dT (algebraMap B T b) = algebraMap B T (dB b))
    (hL : ∀ t, dL (algebraMap T L t) = algebraMap T L (dT t)) :
    ∀ b, dL (algebraMap B L b) = algebraMap B L (dB b) := by
  intro b
  rw [IsScalarTower.algebraMap_apply B T L, hL, hT,
    ← IsScalarTower.algebraMap_apply B T L]

theorem v5MixedDerivationLeft136
    (dT : Derivation k T T) (dL : Derivation k L L) (dR : Derivation k R R)
    (hL : ∀ t, dL (algebraMap T L t) = algebraMap T L (dT t))
    (hR : ∀ t, dR (algebraMap T R t) = algebraMap T R (dT t)) :
    ∀ l, mixedRelativeTensorDerivation dT dL dR hL hR
      (algebraMap L (L ⊗[T] R) l) = algebraMap L (L ⊗[T] R) (dL l) := by
  intro l
  change mixedRelativeTensorDerivation dT dL dR hL hR (l ⊗ₜ[T] (1 : R)) =
    dL l ⊗ₜ[T] (1 : R)
  rw [mixedRelativeTensorDerivation_tmul, Derivation.map_one_eq_zero,
    TensorProduct.tmul_zero, add_zero]

theorem v5MixedDerivationRight136
    (dT : Derivation k T T) (dL : Derivation k L L) (dR : Derivation k R R)
    (hL : ∀ t, dL (algebraMap T L t) = algebraMap T L (dT t))
    (hR : ∀ t, dR (algebraMap T R t) = algebraMap T R (dT t)) (r : R) :
    mixedRelativeTensorDerivation dT dL dR hL hR ((1 : L) ⊗ₜ[T] r) =
      (1 : L) ⊗ₜ[T] dR r := by
  rw [mixedRelativeTensorDerivation_tmul, Derivation.map_one_eq_zero,
    TensorProduct.zero_tmul, zero_add]

def v5KummerAmbientDerivation136
    (dB : Derivation k B B) (dT : Derivation k T T) (dL : Derivation k L L)
    (dR : Derivation k R R) (dW : Derivation k W W)
    (hT : ∀ b, dT (algebraMap B T b) = algebraMap B T (dB b))
    (hL : ∀ t, dL (algebraMap T L t) = algebraMap T L (dT t))
    (hR : ∀ t, dR (algebraMap T R t) = algebraMap T R (dT t))
    (hW : ∀ b, dW (algebraMap B W b) = algebraMap B W (dB b)) :
    Derivation k ((L ⊗[T] R) ⊗[L] (L ⊗[B] W)) ((L ⊗[T] R) ⊗[L] (L ⊗[B] W)) :=
  mixedRelativeTensorDerivation dL
    (mixedRelativeTensorDerivation dT dL dR hL hR)
    (mixedRelativeTensorDerivation dB dL dW (v5DerivationTowerCompatible136 dB dT dL hT hL) hW)
    (v5MixedDerivationLeft136 dT dL dR hL hR)
    (v5MixedDerivationLeft136 dB dL dW (v5DerivationTowerCompatible136 dB dT dL hT hL) hW)

def v5KummerOldAmbientDerivation136
    (dB : Derivation k B B) (dT : Derivation k T T) (dR : Derivation k R R)
    (dW : Derivation k W W)
    (hT : ∀ b, dT (algebraMap B T b) = algebraMap B T (dB b))
    (hR : ∀ t, dR (algebraMap T R t) = algebraMap T R (dT t))
    (hW : ∀ b, dW (algebraMap B W b) = algebraMap B W (dB b)) :
    Derivation k (R ⊗[B] W) (R ⊗[B] W) :=
  mixedRelativeTensorDerivation dB dR dW (v5DerivationTowerCompatible136 dB dT dR hT hR) hW

/-- The honest old-to-Kummer ambient map commutes with the assembled derivations.
Scaling is supplied in the factor derivations, not imposed in this lemma. -/
theorem v5KummerAmbientDifferential136
    (dB : Derivation k B B) (dT : Derivation k T T) (dL : Derivation k L L)
    (dR : Derivation k R R) (dW : Derivation k W W)
    (hT : ∀ b, dT (algebraMap B T b) = algebraMap B T (dB b))
    (hL : ∀ t, dL (algebraMap T L t) = algebraMap T L (dT t))
    (hR : ∀ t, dR (algebraMap T R t) = algebraMap T R (dT t))
    (hW : ∀ b, dW (algebraMap B W b) = algebraMap B W (dB b)) (z : R ⊗[B] W) :
    v5KummerAmbientDerivation136 dB dT dL dR dW hT hL hR hW
      (v5KummerAmbientMap136 (k := k) (T := T) (L := L) z) =
      v5KummerAmbientMap136 (k := k) (T := T) (L := L)
        (v5KummerOldAmbientDerivation136 dB dT dR dW hT hR hW z) := by
  let Γ := v5KummerAmbientMap136 (k := k) (B := B) (T := T) (L := L) (R := R) (W := W)
  let dOld := v5KummerOldAmbientDerivation136 dB dT dR dW hT hR hW
  let dNew := v5KummerAmbientDerivation136 dB dT dL dR dW hT hL hR hW
  change dNew (Γ z) = Γ (dOld z)
  induction z using TensorProduct.induction_on with
  | zero =>
    have hΓ : Γ 0 = 0 := Γ.map_zero'
    have hOld : dOld 0 = 0 := dOld.toLinearMap.map_zero
    have hNew : dNew 0 = 0 := dNew.toLinearMap.map_zero
    rw [hΓ, hOld, hNew, hΓ]
  | add x y hx hy =>
    have hΓ : Γ (x + y) = Γ x + Γ y := Γ.map_add' _ _
    have hOld : dOld (x + y) = dOld x + dOld y := dOld.toLinearMap.map_add' _ _
    have hNew : dNew (Γ x + Γ y) = dNew (Γ x) + dNew (Γ y) := dNew.toLinearMap.map_add' _ _
    have hΓ' : Γ (dOld x + dOld y) = Γ (dOld x) + Γ (dOld y) := Γ.map_add' _ _
    rw [hΓ, hOld, hNew, hΓ', hx, hy]
  | tmul r w =>
    have hΓ (a : R) (b : W) : Γ (a ⊗ₜ[B] b) = ((1 : L) ⊗ₜ[T] a) ⊗ₜ[L] ((1 : L) ⊗ₜ[B] b) :=
      v5KummerAmbientMap136_tmul a b
    have hOld : dOld (r ⊗ₜ[B] w) = dR r ⊗ₜ[B] w + r ⊗ₜ[B] dW w := rfl
    have hNew : dNew ((((1 : L) ⊗ₜ[T] r) ⊗ₜ[L] ((1 : L) ⊗ₜ[B] w))) =
        mixedRelativeTensorDerivation dT dL dR hL hR ((1 : L) ⊗ₜ[T] r) ⊗ₜ[L] ((1 : L) ⊗ₜ[B] w) +
        ((1 : L) ⊗ₜ[T] r) ⊗ₜ[L]
          mixedRelativeTensorDerivation dB dL dW (v5DerivationTowerCompatible136 dB dT dL hT hL) hW
            ((1 : L) ⊗ₜ[B] w) := rfl
    have hΓadd : Γ (dR r ⊗ₜ[B] w + r ⊗ₜ[B] dW w) = Γ (dR r ⊗ₜ[B] w) + Γ (r ⊗ₜ[B] dW w) := Γ.map_add' _ _
    rw [hΓ, hNew, v5MixedDerivationRight136, v5MixedDerivationRight136, hOld, hΓadd, hΓ, hΓ]

theorem v5KummerAmbientHorizontal136
    (dB : Derivation k B B) (dT : Derivation k T T) (dL : Derivation k L L)
    (dR : Derivation k R R) (dW : Derivation k W W)
    (hT : ∀ b, dT (algebraMap B T b) = algebraMap B T (dB b))
    (hL : ∀ t, dL (algebraMap T L t) = algebraMap T L (dT t))
    (hR : ∀ t, dR (algebraMap T R t) = algebraMap T R (dT t))
    (hW : ∀ b, dW (algebraMap B W b) = algebraMap B W (dB b)) (z : R ⊗[B] W)
    (hz : v5KummerOldAmbientDerivation136 dB dT dR dW hT hR hW z = 0) :
    v5KummerAmbientDerivation136 dB dT dL dR dW hT hL hR hW
      (v5KummerAmbientMap136 (k := k) (T := T) (L := L) z) = 0 := by
  rw [v5KummerAmbientDifferential136, hz]
  exact (v5KummerAmbientMap136 (k := k) (T := T) (L := L)).map_zero'
end StrictEUnit
#print axioms StrictEUnit.v5KummerAmbientDerivation136
#print axioms StrictEUnit.v5KummerAmbientDifferential136
#print axioms StrictEUnit.v5KummerAmbientHorizontal136
