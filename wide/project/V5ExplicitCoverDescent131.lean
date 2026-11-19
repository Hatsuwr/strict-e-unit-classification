import V5ExplicitCoverSplit131
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
theorem v5ExplicitCoverDescent131 [Module.FaithfullyFlat B R] {J : Type u} [Finite J]
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) (I : Ideal H)
    (ρ : R →ₐ[B] R ⊗[k] H) (Δ : H →ₐ[k] H ⊗[k] H)
    (he : ∀ r s, e.symm (r ⊗ₜ[B] s) = r • ρ s)
    (hρ : ∀ r, Algebra.TensorProduct.assoc k R H H
      (Algebra.TensorProduct.map (ρ.restrictScalars k) (AlgHom.id k H) (ρ r)) =
      Algebra.TensorProduct.map (AlgHom.id R R) Δ (ρ r))
    (fixed : AlgHom.equalizer
      ((Algebra.TensorProduct.map (AlgHom.id k H) (Ideal.Quotient.mkₐ k I)).comp Δ)
      (Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] (H ⧸ I)) ≃ₐ[k] (J → k)) :
    Module.Finite B (v5CanonicalComponentCover ρ I) ∧
      Module.Flat B (v5CanonicalComponentCover ρ I) ∧
      Algebra.Unramified B (v5CanonicalComponentCover ρ I) :=
  v5_canonicalComponentCover_finite_flat_unramified ρ I
    (v5ExplicitCoverSplit131 e I ρ Δ he hρ fixed)
end StrictEUnit
#print axioms StrictEUnit.v5ExplicitCoverDescent131
