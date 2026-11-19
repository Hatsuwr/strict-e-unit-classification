import V5QuotientRestrictedSquareR129
import V5QuotientChart126
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
universe u v w t
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k : Type t} {B : Type v} {R : Type u} {H : Type w}
  [Field k] [CommRing B] [CommRing R] [CommRing H]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R] [Algebra k H]
/-- Assemble both squares at abstract types before specializing the own cover. -/
def v5ExplicitCoverSplit131 [Module.Flat B R] {J : Type u} [Finite J]
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) (I : Ideal H)
    (ρ : R →ₐ[B] R ⊗[k] H) (Δ : H →ₐ[k] H ⊗[k] H)
    (he : ∀ r s, e.symm (r ⊗ₜ[B] s) = r • ρ s)
    (hρ : ∀ r, Algebra.TensorProduct.assoc k R H H
      (Algebra.TensorProduct.map (ρ.restrictScalars k) (AlgHom.id k H) (ρ r)) =
      Algebra.TensorProduct.map (AlgHom.id R R) Δ (ρ r))
    (fixed : AlgHom.equalizer
      ((Algebra.TensorProduct.map (AlgHom.id k H) (Ideal.Quotient.mkₐ k I)).comp Δ)
      (Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] (H ⧸ I)) ≃ₐ[k] (J → k)) :
    R ⊗[B] v5CanonicalComponentCover ρ I ≃ₐ[R] (J → R) :=
  v5ComponentCoverSplit ρ (Ideal.Quotient.mkₐ k I) _ e.symm
    (v5QuotientOwnTargetChart126 e I)
    (v5RestrictedSquareExplicitR129 e I ρ Δ he hρ)
    (v5QuotientTrivialSquare128 e I) fixed
end StrictEUnit
#print axioms StrictEUnit.v5ExplicitCoverSplit131
