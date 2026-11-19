import V5KummerLiftFirstOrder136
import V5ScaledKummerData136
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
theorem v5KummerLiftFirstOrderOfData136
    (ρ : R →ₐ[T] R ⊗[k] N) (e : R ⊗[T] R ≃ₐ[R] R ⊗[k] N)
    (he : ∀ a b, e (a ⊗ₜ[T] b) = a • ρ b)
    (pL : L →ₐ[k] k) (pR : R →ₐ[k] k) (pW : W →ₐ[k] C)
    (hTmark : ∀ t, pL (algebraMap T L t) = pR (algebraMap T R t))
    (hRmark : ∀ b, algebraMap k C (pR (algebraMap B R b)) = pW (algebraMap B W b))
    (u : (R ⊗[B] W)ˣ) (a c : C) (χ : Nˣ)
    (hlift : V5KummerLiftResult136 ρ pL pR pW hTmark hRmark u a c χ)
    (dB0 : Derivation k B B) (dT0 : Derivation k T T) (dL : Derivation k L L)
    (dR0 : Derivation k R R) (dW0 : Derivation k W W) (coeff : B)
    (data : V5ScaledKummerData136 dB0 dT0 dR0 dW0 dL coeff ρ (u : R ⊗[B] W)) :
    let hB := v5KummerBaseMarks136 pL pR pW hTmark hRmark
    ∃ b : (L ⊗[B] W)ˣ,
      v5MixedMarkedTensor135 pL pW hB (b : L ⊗[B] W) = a ∧
      v5MixedMarkedTensor135 pL pW hB (↑b⁻¹ : L ⊗[B] W) = c ∧
      ∃ ell : L,
        mixedRelativeTensorDerivation (coeff • dB0) dL (algebraMap B W coeff • dW0)
          (v5DerivationTowerCompatible136 (coeff • dB0) (algebraMap B T coeff • dT0) dL data.bt data.tl)
          data.bw (b : L ⊗[B] W) = algebraMap L (L ⊗[B] W) ell * (b : L ⊗[B] W) :=
  v5KummerLiftFirstOrder136 ρ e he pL pR pW hTmark hRmark u a c χ hlift
    (coeff • dB0) (algebraMap B T coeff • dT0) dL
    (algebraMap B R coeff • dR0) (algebraMap B W coeff • dW0)
    data.bt data.tl data.tr data.bw data.coaction data.horizontal
end StrictEUnit
#print axioms StrictEUnit.v5KummerLiftFirstOrderOfData136
