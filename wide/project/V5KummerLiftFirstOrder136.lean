import V5KummerReciprocalValues136
import V5NormalizedFirstOrder136
import V5KummerAmbientDifferential136
import V5KummerCoactionDifferential136
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k B T L R W N C : Type*}
  [Field k] [CommRing B] [CommRing T] [CommRing L] [IsDomain L] [IsPrincipalIdealRing L]
  [CommRing R] [CommRing W] [CommRing N] [CommRing C]
  [Algebra k B] [Algebra k T] [Algebra k L] [Algebra k R] [Algebra k W]
  [Algebra k N] [Algebra k C]
  [Algebra B T] [Algebra T L] [Algebra T R] [Algebra B L] [Algebra B R] [Algebra B W]
  [IsScalarTower B T L] [IsScalarTower B T R]
  [IsScalarTower k B T] [IsScalarTower k B L] [IsScalarTower k B R] [IsScalarTower k B W]
  [IsScalarTower k T L] [IsScalarTower k T R] [Module.FaithfullyFlat T R]
theorem v5KummerLiftFirstOrder136
    (ρ : R →ₐ[T] R ⊗[k] N) (e : R ⊗[T] R ≃ₐ[R] R ⊗[k] N)
    (he : ∀ a b, e (a ⊗ₜ[T] b) = a • ρ b)
    (pL : L →ₐ[k] k) (pR : R →ₐ[k] k) (pW : W →ₐ[k] C)
    (hTmark : ∀ t, pL (algebraMap T L t) = pR (algebraMap T R t))
    (hRmark : ∀ b, algebraMap k C (pR (algebraMap B R b)) = pW (algebraMap B W b))
    (u : (R ⊗[B] W)ˣ) (a c : C) (χ : Nˣ)
    (hlift : V5KummerLiftResult136 ρ pL pR pW hTmark hRmark u a c χ)
    (dB : Derivation k B B) (dT : Derivation k T T) (dL : Derivation k L L)
    (dR : Derivation k R R) (dW : Derivation k W W)
    (hBT : ∀ b, dT (algebraMap B T b) = algebraMap B T (dB b))
    (hTL : ∀ t, dL (algebraMap T L t) = algebraMap T L (dT t))
    (hTR : ∀ t, dR (algebraMap T R t) = algebraMap T R (dT t))
    (hBW : ∀ b, dW (algebraMap B W b) = algebraMap B W (dB b))
    (hρd : ∀ r, tensorDerivation dR (ρ r) = ρ (dR r))
    (hu : v5KummerOldAmbientDerivation136 dB dT dR dW hBT hTR hBW (u : R ⊗[B] W) = 0) :
    let hB := v5KummerBaseMarks136 pL pR pW hTmark hRmark
    ∃ b : (L ⊗[B] W)ˣ,
      v5MixedMarkedTensor135 pL pW hB (b : L ⊗[B] W) = a ∧
      v5MixedMarkedTensor135 pL pW hB (↑b⁻¹ : L ⊗[B] W) = c ∧
      ∃ ell : L,
        mixedRelativeTensorDerivation dB dL dW (v5DerivationTowerCompatible136 dB dT dL hBT hTL) hBW
          (b : L ⊗[B] W) = algebraMap L (L ⊗[B] W) ell * (b : L ⊗[B] W) := by
  obtain ⟨v,hv,b,hprod,hm,hmi⟩ := hlift
  let pS := v5MarkedBaseChangePoint135 pL pR hTmark
  let dS := mixedRelativeTensorDerivation dT dL dR hTL hTR
  let dWK := mixedRelativeTensorDerivation dB dL dW
    (v5DerivationTowerCompatible136 dB dT dL hBT hTL) hBW
  let dM := v5KummerAmbientDerivation136 dB dT dL dR dW hBT hTL hTR hBW
  let γ : (L ⊗[T] R) →ₐ[L] (L ⊗[T] R) ⊗[L] (L ⊗[B] W) := Algebra.TensorProduct.includeLeft
  let φ : (L ⊗[B] W) →ₐ[L] (L ⊗[T] R) ⊗[L] (L ⊗[B] W) := Algebra.TensorProduct.includeRight
  let Γ := v5KummerAmbientMap136 (k := k) (B := B) (T := T) (L := L) (R := R) (W := W)
  letI := v5KummerBaseChangeFaithfullyFlat135 (T := T) (L := L) (R := R)
  have hγd (s : L ⊗[T] R) : dM (γ s) = γ (dS s) := by
    change mixedRelativeTensorDerivation dL dS dWK _ _ (s ⊗ₜ[L] 1) = dS s ⊗ₜ[L] 1
    rw [mixedRelativeTensorDerivation_tmul, Derivation.map_one_eq_zero, TensorProduct.tmul_zero, add_zero]
  have hφd (w : L ⊗[B] W) : dM (φ w) = φ (dWK w) := by
    change mixedRelativeTensorDerivation dL dS dWK _ _ (1 ⊗ₜ[L] w) = 1 ⊗ₜ[L] dWK w
    rw [mixedRelativeTensorDerivation_tmul, Derivation.map_one_eq_zero, TensorProduct.zero_tmul, zero_add]
  have hprod' : φ (b : L ⊗[B] W) = Γ (u : R ⊗[B] W) * γ (v5NormalizeMarkedUnit pS v : L ⊗[T] R) :=
    congrArg Units.val hprod
  have hρS := v5KummerCoaction135_differential136 dT dL dR hTL hTR ρ hρd
  have hzero := v5KummerAmbientHorizontal136 dB dT dL dR dW hBT hTL hTR hBW (u : R ⊗[B] W) hu
  obtain ⟨ell,hell⟩ := v5NormalizedCorrectedFirstOrder136
    (v5KummerCoaction135 ρ) (v5KummerBaseChangeChart135 e)
    (v5KummerBaseChangeChart135_tmul e ρ he) γ φ
    (v5_faithful_includeRight_injective135 (L := L) (S := L ⊗[T] R) (W := L ⊗[B] W))
    dS dWK dM (fun s => (hρS s).symm) hγd hφd pS χ⁻¹ v hv
    (Γ (u : R ⊗[B] W)) hzero (b : L ⊗[B] W) hprod'
  exact ⟨b,hm,hmi,ell,hell⟩
end StrictEUnit
#print axioms StrictEUnit.v5KummerLiftFirstOrder136
