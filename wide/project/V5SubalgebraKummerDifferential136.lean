import V5KummerCoactionDifferential136
import V5ScaledCoactionDifferential136
import V5CoverRestrictedCoaction135
import V5CoverDifferential126
noncomputable section
open scoped TensorProduct
set_option Elab.async false
set_option maxHeartbeats 600000
set_option maxRecDepth 1600
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k B R H L : Type*} [Field k] [CommRing B] [CommRing R] [CommRing H] [CommRing L]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
  [Algebra k H] [Algebra k L]
def v5CoordinateEuler136 {U : Type*} [CommRing U] [Algebra k U] [Algebra B U]
    (z : B) (d : Derivation k U U) : Derivation k U U := algebraMap B U z • d
/-- Assemble cover restriction, Euler scaling, balance and quotient differential
coaction at abstract types before specializing the actual candidate. -/
def v5SubalgebraKummerDifferential136
    (ρ : R →ₐ[B] R ⊗[k] H) (I : Ideal H)
    (dR : Derivation k R R)
    (hd : ∀ r, tensorDerivation dR (ρ r) = ρ (dR r))
    (z : B) (q : ℕ) (dL : Derivation k L L)
    (α : v5CanonicalComponentCover ρ I →ₐ[k] L)
    (hα : ∀ t, dL (α t) = (q : L) *
      α (v5CoordinateEuler136 z (v5ComponentCoverDerivation126 ρ (Ideal.Quotient.mkₐ k I) dR hd) t)) := by
  let T := v5CanonicalComponentCover ρ I
  let dT := v5ComponentCoverDerivation126 ρ (Ideal.Quotient.mkₐ k I) dR hd
  let θT := v5CoordinateEuler136 z dT
  let c := algebraMap B R z
  let θR := v5CoordinateEuler136 z dR
  let τ := v5CoverRestrictedCoaction135 ρ I
  letI : IsScalarTower k T R :=
    IsScalarTower.of_algebraMap_eq (fun a => ((T.val.restrictScalars k).commutes a).symm)
  letI : Algebra T L := α.toAlgebra
  letI : IsScalarTower k T L :=
    IsScalarTower.of_algebraMap_eq (fun a => (α.commutes a).symm)
  have hL (t : T) : dL (algebraMap T L t) = algebraMap T L ((q • θT) t) := by
    change dL (α t) = α (q • θT t)
    rw [map_nsmul, nsmul_eq_mul]
    exact hα t
  have hR (t : T) : (q • θR) (algebraMap T R t) = algebraMap T R ((q • θT) t) := by
    change q • (c * dR (t : R)) = q • ((θT t : T) : R)
    rfl
  have hc : ρ c = c ⊗ₜ[k] (1 : H) := ρ.commutes z
  have hρθ (r : R) : tensorDerivation θR (ρ r) = ρ (θR r) :=
    v5_scaled_coaction_differential136 ρ dR hd c hc r
  have hτθ (r : R) : tensorDerivation θR (τ r) = τ (θR r) := by
    change tensorDerivation θR
      (Algebra.TensorProduct.map (AlgHom.id B R) (Ideal.Quotient.mkₐ k I) (ρ r)) =
      Algebra.TensorProduct.map (AlgHom.id B R) (Ideal.Quotient.mkₐ k I) (ρ (θR r))
    rw [v5_tensorDerivation_map_right_factor126, hρθ]
  exact v5KummerDifferentialData136 (k := k) (T := T) (L := L) (R := R) (N := H ⧸ I) (q • θT) dL (q • θR) hL hR τ
    (v5_nsmul_coaction_differential136 τ θR hτθ q)
end StrictEUnit
#print axioms StrictEUnit.v5SubalgebraKummerDifferential136
