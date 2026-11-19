import V5ExplicitRelativeComparison134
import V5RelativeChartCounit130
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
universe u v w t
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k : Type t} {B : Type v} {R : Type u} {H : Type w}
  [Field k] [CommRing B] [CommRing R] [CommRing H]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R] [Algebra k H]
theorem v5ExplicitRelativeAssembly134 [Module.FaithfullyFlat B R]
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
      C x j = algebraMap k (H ⧸ I) (fixed x j))
    (p : H ⧸ I →ₐ[k] k) (i : J) (u : H ⧸ I →ₐ[k] H ⧸ I)
    (hiC : ∀ h, C h i = u (Ideal.Quotient.mkₐ k I h)) :
    Module.FaithfullyFlat (v5CanonicalComponentCover ρ I) R ∧
      ∃ rel : R ⊗[v5CanonicalComponentCover ρ I] R ≃ₐ[R] R ⊗[k] (H ⧸ I),
        ∀ a b, rel (a ⊗ₜ[v5CanonicalComponentCover ρ I] b) =
          (e.symm.trans (v5TensorComponentChart132 C)) (a ⊗ₜ[B] b) i := by
  let chart := e.symm.trans (v5TensorComponentChart132 C)
  let E := (v5EqualizerTensorChart131
    (v5ComponentOwnAction ρ (Ideal.Quotient.mkₐ k I)) v5ComponentOwnTrivial
    ((Algebra.TensorProduct.map (AlgHom.id k H) (Ideal.Quotient.mkₐ k I)).comp Δ)
    Algebra.TensorProduct.includeLeft e.symm (v5QuotientOwnTargetChart126 e I)
    (v5RestrictedSquareExplicitR129 e I ρ Δ he hρ)
    (v5QuotientTrivialSquare128 e I)).trans (v5TensorScalarChart132 _ fixed)
  have hr := v5ExplicitCoverRight133 e I ρ Δ he hρ fixed C hc
  have hcoord (z : R ⊗[k] H) :
      v5TensorComponentChart132 C z i =
        Algebra.TensorProduct.map (AlgHom.id R R) u
          (Algebra.TensorProduct.map (AlgHom.id R R) (Ideal.Quotient.mkₐ k I) z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r h =>
      change r ⊗ₜ[k] C h i = r ⊗ₜ[k] u (Ideal.Quotient.mkₐ k I h)
      rw [hiC]
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  have hi (t : v5CanonicalComponentCover ρ I) :
      chart (1 ⊗ₜ[B] (t : R)) i = (t : R) ⊗ₜ[k] (1 : H ⧸ I) := by
    change v5TensorComponentChart132 C (e.symm (1 ⊗ₜ[B] (t : R))) i = _
    rw [he, one_smul, hcoord]
    have ht := t.property
    change Algebra.TensorProduct.map (AlgHom.id R R) (Ideal.Quotient.mkₐ k I)
      (ρ (t : R)) = (t : R) ⊗ₜ[k] (1 : H ⧸ I) at ht
    rw [ht]
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
  exact ⟨v5_relative_flat_from_right130 chart E hr,
    v5_relative_identity_tensor_chart130 p i chart E hr hi⟩
end StrictEUnit
#print axioms StrictEUnit.v5ExplicitRelativeAssembly134
