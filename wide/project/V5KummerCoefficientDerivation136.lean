import V5ScaledKummerData136
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
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
/-- Construct the coefficient derivation while the cover is an abstract ring,
so later subtype specializations do not synthesize a new scalar action on its
derivation space. -/
def v5ScaledKummerCoeffDerivation136
    (dB0 : Derivation k B B) (dT0 : Derivation k T T) (dR0 : Derivation k R R)
    (dW0 : Derivation k W W) (dL : Derivation k L L) (coeff : B)
    (ρ : R →ₐ[T] R ⊗[k] N) (z : R ⊗[B] W)
    (data : V5ScaledKummerData136 dB0 dT0 dR0 dW0 dL coeff ρ z) :
    Derivation k (L ⊗[B] W) (L ⊗[B] W) :=
  mixedRelativeTensorDerivation (coeff • dB0) dL (algebraMap B W coeff • dW0)
    (v5DerivationTowerCompatible136 (coeff • dB0) (algebraMap B T coeff • dT0) dL data.bt data.tl)
    data.bw

@[simp] theorem v5ScaledKummerCoeffDerivation136_tmul
    (dB0 : Derivation k B B) (dT0 : Derivation k T T) (dR0 : Derivation k R R)
    (dW0 : Derivation k W W) (dL : Derivation k L L) (coeff : B)
    (ρ : R →ₐ[T] R ⊗[k] N) (z : R ⊗[B] W)
    (data : V5ScaledKummerData136 dB0 dT0 dR0 dW0 dL coeff ρ z) (l : L) (w : W) :
    v5ScaledKummerCoeffDerivation136 dB0 dT0 dR0 dW0 dL coeff ρ z data (l ⊗ₜ[B] w) =
      dL l ⊗ₜ[B] w + l ⊗ₜ[B] (algebraMap B W coeff * dW0 w) := rfl
end StrictEUnit
#print axioms StrictEUnit.v5ScaledKummerCoeffDerivation136
#print axioms StrictEUnit.v5ScaledKummerCoeffDerivation136_tmul
