import V5ExplicitCoverRight133
import V5RelativeFlatFromRight130
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
universe u v w t
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k : Type t} {B : Type v} {R : Type u} {H : Type w}
  [Field k] [CommRing B] [CommRing R] [CommRing H]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R] [Algebra k H]
theorem v5ExplicitRelativeComparison134 [Module.FaithfullyFlat B R]
    {J : Type u} [Fintype J] [DecidableEq J]
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) (I : Ideal H) [Nontrivial (H ⧸ I)]
    (ρ : R →ₐ[B] R ⊗[k] H) (Δ : H →ₐ[k] H ⊗[k] H)
    (he : ∀ r s, e.symm (r ⊗ₜ[B] s) = r • ρ s)
    (hρ : ∀ r, Algebra.TensorProduct.assoc k R H H
      (Algebra.TensorProduct.map (ρ.restrictScalars k) (AlgHom.id k H) (ρ r)) =
      Algebra.TensorProduct.map (AlgHom.id R R) Δ (ρ r))
    (fixed : AlgHom.equalizer
      ((Algebra.TensorProduct.map (AlgHom.id k H) (Ideal.Quotient.mkₐ k I)).comp Δ)
      (Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] (H ⧸ I)) ≃ₐ[k] (J → k))
    (C : H ≃ₐ[k] (J → H ⧸ I))
    (hc : ∀ x : AlgHom.equalizer
      ((Algebra.TensorProduct.map (AlgHom.id k H) (Ideal.Quotient.mkₐ k I)).comp Δ)
      (Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] (H ⧸ I)), ∀ j,
      C x j = algebraMap k (H ⧸ I) (fixed x j)) :
    ∃ chart : R ⊗[B] R ≃ₐ[R] (J → R ⊗[k] (H ⧸ I)),
      ∃ E : R ⊗[B] v5CanonicalComponentCover ρ I ≃ₐ[R] (J → R),
        (∀ t : v5CanonicalComponentCover ρ I, ∀ j,
          chart (1 ⊗ₜ[B] (t : R)) j = E (1 ⊗ₜ[B] t) j ⊗ₜ[k] (1 : H ⧸ I)) ∧
        Module.FaithfullyFlat (v5CanonicalComponentCover ρ I) R := by
  let chart := e.symm.trans (v5TensorComponentChart132 C)
  let E := (v5EqualizerTensorChart131
    (v5ComponentOwnAction ρ (Ideal.Quotient.mkₐ k I)) v5ComponentOwnTrivial
    ((Algebra.TensorProduct.map (AlgHom.id k H) (Ideal.Quotient.mkₐ k I)).comp Δ)
    Algebra.TensorProduct.includeLeft e.symm (v5QuotientOwnTargetChart126 e I)
    (v5RestrictedSquareExplicitR129 e I ρ Δ he hρ)
    (v5QuotientTrivialSquare128 e I)).trans (v5TensorScalarChart132 _ fixed)
  have hr := v5ExplicitCoverRight133 e I ρ Δ he hρ fixed C hc
  exact ⟨chart, E, hr, v5_relative_flat_from_right130 chart E hr⟩
end StrictEUnit
#print axioms StrictEUnit.v5ExplicitRelativeComparison134
