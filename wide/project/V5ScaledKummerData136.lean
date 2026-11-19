import V5KummerAmbientDifferential136
import V5MixedDerivationScale136
import V5ScaledCoactionDifferential136
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
set_option maxHeartbeats 600000
set_option maxRecDepth 1600
set_option linter.unusedSectionVars false
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k B T L R W N : Type*}
  [CommRing k] [CommRing B] [CommRing T] [CommRing L] [CommRing R]
  [CommRing W] [CommRing N]
  [Algebra k B] [Algebra k T] [Algebra k L] [Algebra k R] [Algebra k W] [Algebra k N]
  [Algebra B T] [Algebra B L] [Algebra B R] [Algebra B W]
  [Algebra T L] [Algebra T R]
  [IsScalarTower k B T] [IsScalarTower k B L] [IsScalarTower k B R] [IsScalarTower k B W]
  [IsScalarTower k T L] [IsScalarTower k T R]
  [IsScalarTower B T L] [IsScalarTower B T R]

/-- Compatibility survives scaling by the image of a common base coefficient. -/
theorem v5ScaledBaseCompatible136
    (dB0 : Derivation k B B) (dR0 : Derivation k R R)
    (hR0 : ∀ b, dR0 (algebraMap B R b) = algebraMap B R (dB0 b)) (c : B) :
    ∀ b, (algebraMap B R c • dR0) (algebraMap B R b) = algebraMap B R ((c • dB0) b) := by
  intro b
  change algebraMap B R c * dR0 (algebraMap B R b) = algebraMap B R (c * dB0 b)
  rw [hR0, map_mul]

/-- The T→R square uses the same B coefficient on both sides of the tower. -/
theorem v5ScaledTowerCompatible136
    (dT0 : Derivation k T T) (dR0 : Derivation k R R)
    (hR0 : ∀ t, dR0 (algebraMap T R t) = algebraMap T R (dT0 t)) (c : B) :
    ∀ t, (algebraMap B R c • dR0) (algebraMap T R t) =
      algebraMap T R ((algebraMap B T c • dT0) t) := by
  intro t
  change algebraMap B R c * dR0 (algebraMap T R t) =
    algebraMap T R (algebraMap B T c * dT0 t)
  rw [hR0, map_mul, ← IsScalarTower.algebraMap_apply B T R]

/-- This is the supplied Kummer Euler compatibility expressed as the scaled
T-derivation expected by the ambient assembly. -/
theorem v5ScaledKummerCompatible136
    (dT0 : Derivation k T T) (dL : Derivation k L L) (c : B)
    (hL : ∀ t, dL (algebraMap T L t) =
      algebraMap T L (algebraMap B T c * dT0 t)) :
    ∀ t, dL (algebraMap T L t) = algebraMap T L ((algebraMap B T c • dT0) t) :=
  hL

/-- Coefficient invariance follows from the T-algebra coaction itself. -/
theorem v5ScaledOwnCoaction136
    (ρ : R →ₐ[T] R ⊗[k] N) (dR0 : Derivation k R R)
    (hρ0 : ∀ r, tensorDerivation dR0 (ρ r) = ρ (dR0 r)) (c : B) :
    ∀ r, tensorDerivation (algebraMap B R c • dR0) (ρ r) =
      ρ ((algebraMap B R c • dR0) r) := by
  have hc : ρ (algebraMap B R c) = algebraMap B R c ⊗ₜ[k] (1 : N) := by
    rw [IsScalarTower.algebraMap_apply B T R]
    exact ρ.commutes (algebraMap B T c)
  exact v5_scaled_coaction_differential136 ρ dR0 hρ0 (algebraMap B R c) hc

/-- The actual mixed derivation built from the three scaled factor derivations
annihilates every original horizontal element. -/
theorem v5ScaledOldMixedHorizontal136
    (dB0 : Derivation k B B) (dR0 : Derivation k R R) (dW0 : Derivation k W W)
    (hR0 : ∀ b, dR0 (algebraMap B R b) = algebraMap B R (dB0 b))
    (hW0 : ∀ b, dW0 (algebraMap B W b) = algebraMap B W (dB0 b))
    (c : B) (z : R ⊗[B] W)
    (hz : mixedRelativeTensorDerivation dB0 dR0 dW0 hR0 hW0 z = 0) :
    mixedRelativeTensorDerivation (c • dB0) (algebraMap B R c • dR0) (algebraMap B W c • dW0)
      (v5ScaledBaseCompatible136 dB0 dR0 hR0 c)
      (v5ScaledBaseCompatible136 dB0 dW0 hW0 c) z = 0 := by
  apply v5MixedDerivationScaleHorizontal136 dB0 dR0 dW0 hR0 hW0 c
    (algebraMap B R c • dR0) (algebraMap B W c • dW0) _
    (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) z hz

/-- All scaled differential inputs needed by the same marked Kummer lift,
with the old mixed derivation built from these very compatibility fields. -/
structure V5ScaledKummerData136
    (dB0 : Derivation k B B) (dT0 : Derivation k T T) (dR0 : Derivation k R R)
    (dW0 : Derivation k W W) (dL : Derivation k L L) (c : B)
    (ρ : R →ₐ[T] R ⊗[k] N) (z : R ⊗[B] W) : Prop where
  bt : ∀ b, (algebraMap B T c • dT0) (algebraMap B T b) = algebraMap B T ((c • dB0) b)
  tl : ∀ t, dL (algebraMap T L t) = algebraMap T L ((algebraMap B T c • dT0) t)
  tr : ∀ t, (algebraMap B R c • dR0) (algebraMap T R t) =
    algebraMap T R ((algebraMap B T c • dT0) t)
  bw : ∀ b, (algebraMap B W c • dW0) (algebraMap B W b) = algebraMap B W ((c • dB0) b)
  coaction : ∀ r, tensorDerivation (algebraMap B R c • dR0) (ρ r) =
    ρ ((algebraMap B R c • dR0) r)
  horizontal : v5KummerOldAmbientDerivation136
    (c • dB0) (algebraMap B T c • dT0) (algebraMap B R c • dR0) (algebraMap B W c • dW0)
    bt tr bw z = 0

/-- The scaled Kummer differential data are derived from ordinary compatibility,
the checked Kummer Euler square, ordinary own differential coaction, and
original horizontality. -/
theorem v5ScaledKummerData136
    (dB0 : Derivation k B B) (dT0 : Derivation k T T) (dR0 : Derivation k R R)
    (dW0 : Derivation k W W) (dL : Derivation k L L)
    (hT0 : ∀ b, dT0 (algebraMap B T b) = algebraMap B T (dB0 b))
    (hR0 : ∀ t, dR0 (algebraMap T R t) = algebraMap T R (dT0 t))
    (hW0 : ∀ b, dW0 (algebraMap B W b) = algebraMap B W (dB0 b))
    (c : B)
    (hL : ∀ t, dL (algebraMap T L t) = algebraMap T L (algebraMap B T c * dT0 t))
    (ρ : R →ₐ[T] R ⊗[k] N)
    (hρ0 : ∀ r, tensorDerivation dR0 (ρ r) = ρ (dR0 r))
    (z : R ⊗[B] W)
    (hz : mixedRelativeTensorDerivation dB0 dR0 dW0
      (v5DerivationTowerCompatible136 dB0 dT0 dR0 hT0 hR0) hW0 z = 0) :
    V5ScaledKummerData136 dB0 dT0 dR0 dW0 dL c ρ z := by
  refine ⟨v5ScaledBaseCompatible136 dB0 dT0 hT0 c,
    v5ScaledKummerCompatible136 dT0 dL c hL,
    v5ScaledTowerCompatible136 dT0 dR0 hR0 c,
    v5ScaledBaseCompatible136 dB0 dW0 hW0 c,
    v5ScaledOwnCoaction136 ρ dR0 hρ0 c, ?_⟩
  exact v5ScaledOldMixedHorizontal136 dB0 dR0 dW0
    (v5DerivationTowerCompatible136 dB0 dT0 dR0 hT0 hR0) hW0 c z hz
end StrictEUnit
#print axioms StrictEUnit.v5ScaledBaseCompatible136
#print axioms StrictEUnit.v5ScaledTowerCompatible136
#print axioms StrictEUnit.v5ScaledKummerCompatible136
#print axioms StrictEUnit.v5ScaledOwnCoaction136
#print axioms StrictEUnit.v5ScaledOldMixedHorizontal136
#print axioms StrictEUnit.v5ScaledKummerData136
