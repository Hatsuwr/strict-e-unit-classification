import V5ScaledKummerData136
import V5SubalgebraKummerDifferential136
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
set_option Elab.async false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option maxRecDepth 1800
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k B R H W L : Type*} [Field k] [CommRing B] [CommRing R] [CommRing H]
  [CommRing W] [CommRing L] [Algebra k B] [Algebra k R] [Algebra B R]
  [IsScalarTower k B R] [Algebra k H] [Algebra k W] [Algebra B W]
  [IsScalarTower k B W] [Algebra k L]
/-- Explicit coordinate derivation evaluation without heterogeneous scalar inference. -/
theorem v5CoordinateEuler_apply136 {U : Type*} [CommRing U] [Algebra k U] [Algebra B U]
    (z : B) (d : Derivation k U U) (u : U) :
    v5CoordinateEuler136 z d u = algebraMap B U z * d u := rfl
/-- A coordinate scaling identity, stated before specializing to subtype rings. -/
theorem v5CoordinateEuler_nat_mul136 {U : Type*} [CommRing U] [Algebra k U] [Algebra B U]
    (z : B) (d : Derivation k U U) (q : ℕ) (u : U) :
    v5CoordinateEuler136 ((q : B) * z) d u = q • v5CoordinateEuler136 z d u := by
  change algebraMap B U ((q : B) * z) * d u = q • (algebraMap B U z * d u)
  rw [map_mul, map_natCast, nsmul_eq_mul, mul_assoc]
/-- Convert a q-scaled Euler square to scaling by the single common coefficient. -/
theorem v5CoordinateEuler_scaled_map136
    {U : Type*} [CommRing U] [Algebra k U] [Algebra B U]
    (z : B) (d : Derivation k U U) (q : ℕ) (dL : Derivation k L L)
    (α : U →ₐ[k] L)
    (h : ∀ u, dL (α u) = (q : L) * α (v5CoordinateEuler136 z d u)) :
    ∀ u, dL (α u) = α (v5CoordinateEuler136 ((q : B) * z) d u) := by
  intro u
  rw [v5CoordinateEuler_nat_mul136, map_nsmul, nsmul_eq_mul]
  exact h u
/-- Identify a common scaled coordinate derivation by its coefficient image. -/
theorem v5CoordinateEuler_scaled_value136
    {U : Type*} [CommRing U] [Algebra k U] [Algebra B U]
    (z : B) (d : Derivation k U U) (q : ℕ) (a : U)
    (ha : algebraMap B U z = a) (D : U → U) (hD : ∀ u, D u = a * d u) :
    ∀ u, v5CoordinateEuler136 ((q : B) * z) d u = q • D u := by
  intro u
  rw [v5CoordinateEuler_nat_mul136, hD]
  change q • (algebraMap B U z * d u) = q • (a * d u)
  rw [ha]
/-- The canonical component cover supplies all ordinary squares and the quotient
coaction square; a single Euler-compatible Kummer map supplies the new base square.
Every old mixed constant then supplies the remaining horizontality field. -/
def v5SubalgebraScaledKummerData136
    (ρ : R →ₐ[B] R ⊗[k] H) (I : Ideal H)
    (dB0 : Derivation k B B) (dR0 : Derivation k R R)
    (hBR0 : ∀ b, dR0 (algebraMap B R b) = algebraMap B R (dB0 b))
    (hd : ∀ r, tensorDerivation dR0 (ρ r) = ρ (dR0 r))
    (dW0 : Derivation k W W)
    (hBW0 : ∀ b, dW0 (algebraMap B W b) = algebraMap B W (dB0 b))
    (c : B) (dL : Derivation k L L)
    (α : v5CanonicalComponentCover ρ I →ₐ[k] L)
    (hα : ∀ t, dL (α t) = α (v5CoordinateEuler136 c
      (v5ComponentCoverDerivation126 ρ (Ideal.Quotient.mkₐ k I) dR0 hd) t)) := by
  let T := v5CanonicalComponentCover ρ I
  let dT0 := v5ComponentCoverDerivation126 ρ (Ideal.Quotient.mkₐ k I) dR0 hd
  let τ := v5CoverRestrictedCoaction135 ρ I
  letI : IsScalarTower k T R :=
    IsScalarTower.of_algebraMap_eq (fun a => ((T.val.restrictScalars k).commutes a).symm)
  letI : Algebra T L := α.toAlgebra
  letI : IsScalarTower k T L :=
    IsScalarTower.of_algebraMap_eq (fun a => (α.commutes a).symm)
  letI : Algebra B L := (α.toRingHom.comp (algebraMap B T)).toAlgebra
  letI : IsScalarTower B T L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower k B L := IsScalarTower.of_algebraMap_eq (fun a => by
    change algebraMap k L a = α (algebraMap B T (algebraMap k B a))
    rw [← IsScalarTower.algebraMap_apply k B T, α.commutes])
  have hT0 : ∀ b, dT0 (algebraMap B T b) = algebraMap B T (dB0 b) :=
    v5ComponentCoverDerivation126_base ρ (Ideal.Quotient.mkₐ k I) dR0 hd dB0 hBR0
  have hTR0 : ∀ t, dR0 (algebraMap T R t) = algebraMap T R (dT0 t) := fun _ => rfl
  have hτ : ∀ r, tensorDerivation dR0 (τ r) = τ (dR0 r) := by
    intro r
    change tensorDerivation dR0
      (Algebra.TensorProduct.map (AlgHom.id B R) (Ideal.Quotient.mkₐ k I) (ρ r)) =
      Algebra.TensorProduct.map (AlgHom.id B R) (Ideal.Quotient.mkₐ k I) (ρ (dR0 r))
    rw [v5_tensorDerivation_map_right_factor126, hd]
  exact fun (z : R ⊗[B] W)
    (hz : mixedRelativeTensorDerivation dB0 dR0 dW0 hBR0 hBW0 z = 0) =>
    v5ScaledKummerData136 (k := k) (B := B) (T := T) (L := L) (R := R) (W := W) (N := H ⧸ I)
      dB0 dT0 dR0 dW0 dL hT0 hTR0 hBW0 c hα τ hτ z hz
end StrictEUnit
#print axioms StrictEUnit.v5CoordinateEuler_apply136
#print axioms StrictEUnit.v5CoordinateEuler_nat_mul136
#print axioms StrictEUnit.v5CoordinateEuler_scaled_value136
#print axioms StrictEUnit.v5CoordinateEuler_scaled_map136
#print axioms StrictEUnit.v5SubalgebraScaledKummerData136
