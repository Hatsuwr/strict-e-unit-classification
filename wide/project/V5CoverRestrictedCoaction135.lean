import V5UntwistRelative135
import V5RestrictComponentCoaction
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k B R H N : Type*} [Field k] [CommRing B] [CommRing R]
  [CommRing H] [CommRing N] [Algebra k B] [Algebra k R]
  [Algebra B R] [IsScalarTower k B R] [Algebra k H] [Algebra k N]
def v5CoverRestrictedCoaction135 (ρ : R →ₐ[B] R ⊗[k] H) (I : Ideal H) :
    R →ₐ[v5CanonicalComponentCover ρ I] R ⊗[k] (H ⧸ I) :=
  { (v5ComponentOwnAction ρ (Ideal.Quotient.mkₐ k I)).toRingHom with
    commutes' := by
      intro t
      change (v5ComponentOwnAction ρ (Ideal.Quotient.mkₐ k I)) (t : R) =
        (v5ComponentOwnTrivial (B := B) (k := k) (R := R) (N := H ⧸ I)) (t : R)
      exact t.property }

theorem v5MapIdLinear135 {Q : Type*} [CommRing Q] [Algebra k Q] (D : H →ₐ[k] Q) (z : R ⊗[k] H) :
      Algebra.TensorProduct.map (AlgHom.id R R) D z =
        D.toLinearMap.lTensor R z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem v5RestrictedCoassoc135 (ρ : R →ₐ[B] R ⊗[k] H)
    (q : H →ₐ[k] N) (ΔH : H →ₐ[k] H ⊗[k] H) (ΔN : N →ₐ[k] N ⊗[k] N)
    (hq : ∀ h, ΔN (q h) = TensorProduct.map q.toLinearMap q.toLinearMap (ΔH h))
    (hρ : ∀ r, Algebra.TensorProduct.assoc k R H H
      (Algebra.TensorProduct.map (ρ.restrictScalars k) (AlgHom.id k H) (ρ r)) =
      Algebra.TensorProduct.map (AlgHom.id R R) ΔH (ρ r)) (r : R) :
    Algebra.TensorProduct.assoc k R N N
      (Algebra.TensorProduct.map
        ((v5ComponentOwnAction ρ q).restrictScalars k) (AlgHom.id k N)
        (v5ComponentOwnAction ρ q r)) =
      Algebra.TensorProduct.map (AlgHom.id R R) ΔN (v5ComponentOwnAction ρ q r) := by
  have hlin (r : R) :
      TensorProduct.assoc k R H H ((ρ.restrictScalars k).toLinearMap.rTensor H (ρ r)) =
        ΔH.toLinearMap.lTensor R (ρ r) := by
    simpa only [v5MapIdLinear135] using hρ r
  have h := v5RestrictComponentCoaction_coassoc (ρ.restrictScalars k) q ΔH ΔN hq hlin r
  simpa only [← v5MapIdLinear135] using h
end StrictEUnit
#print axioms StrictEUnit.v5CoverRestrictedCoaction135
#print axioms StrictEUnit.v5RestrictedCoassoc135
