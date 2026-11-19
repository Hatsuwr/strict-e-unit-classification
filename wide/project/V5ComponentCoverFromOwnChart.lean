import V5ComponentCover
import V5OwnTorsorSquare
import CandidateCoaction

noncomputable section
open scoped TensorProduct
namespace StrictEUnit
universe u v w w' l
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule

variable {B : Type v} {k : Type w} {R : Type u} {H : Type w'} {N : Type l}
  [CommRing B] [Field k] [CommRing R] [CommRing H] [CommRing N]
  [Algebra B R] [Algebra k B] [Algebra k R] [IsScalarTower k B R] [Algebra k H] [Algebra k N]

theorem v5_ownChart_tmul_smul
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) (r s : R) :
    e.symm (r ⊗ₜ[B] s) = r • inverseMultiplicationCoaction e s := by
  change (e.symm.toAlgHom.restrictScalars B) (r ⊗ₜ[B] s) = _
  rw [← relativeCandidateCanonical_eq_inverse e, relativeCandidateCanonical_tmul, Algebra.smul_def]
  rfl

/-- The own canonical chart supplies both squares, so the split model needs
only the actual coassociativity law and the fixed-algebra equivalence. -/
def v5ComponentCoverSplitFromOwnChart [Module.Flat B R] {J : Type u} [Finite J]
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) (q : H →ₐ[k] N)
    (Δ : H →ₐ[k] H ⊗[k] H)
    (hρ : ∀ r, Algebra.TensorProduct.assoc k R H H
      (Algebra.TensorProduct.map ((inverseMultiplicationCoaction e).restrictScalars k)
        (AlgHom.id k H) (inverseMultiplicationCoaction e r)) =
      Algebra.TensorProduct.map (AlgHom.id k R) Δ (inverseMultiplicationCoaction e r))
    (fixed : AlgHom.equalizer ((Algebra.TensorProduct.map (AlgHom.id k H) q).comp Δ)
      (Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] N) ≃ₐ[k] (J → k)) :
    R ⊗[B] v5ComponentCoverAlgebra (inverseMultiplicationCoaction e) q ≃ₐ[R] (J → R) :=
  v5ComponentCoverSplit (inverseMultiplicationCoaction e) q
    ((Algebra.TensorProduct.map (AlgHom.id k H) q).comp Δ) e.symm
    (v5OwnTorsorTargetChartR e.symm)
    (v5OwnRestrictedTorsorSquareR e.symm (inverseMultiplicationCoaction e) Δ q
      (v5_ownChart_tmul_smul e) hρ)
    (v5OwnTrivialTorsorSquareR e.symm) fixed

/-- Canonical quotient presentation avoids concrete quotient-instance search
when applying the general cover theorem to a heavily bundled algebra. -/
def v5CanonicalComponentCover (ρ : R →ₐ[B] R ⊗[k] H) (I : Ideal H) :=
  v5ComponentCoverAlgebra ρ (Ideal.Quotient.mkₐ k I)

def v5CanonicalComponentCoverMark (ρ : R →ₐ[B] R ⊗[k] H) (I : Ideal H)
    (p : R →ₐ[k] k) :=
  v5ComponentCoverMark ρ (Ideal.Quotient.mkₐ k I) p

def v5CanonicalComponentCoverSplit [Module.Flat B R] {J : Type u} [Finite J]
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) (I : Ideal H)
    (Δ : H →ₐ[k] H ⊗[k] H)
    (hρ : ∀ r, Algebra.TensorProduct.assoc k R H H
      (Algebra.TensorProduct.map ((inverseMultiplicationCoaction e).restrictScalars k)
        (AlgHom.id k H) (inverseMultiplicationCoaction e r)) =
      Algebra.TensorProduct.map (AlgHom.id k R) Δ (inverseMultiplicationCoaction e r))
    (fixed : AlgHom.equalizer
      ((Algebra.TensorProduct.map (AlgHom.id k H) (Ideal.Quotient.mkₐ k I)).comp Δ)
      (Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] (H ⧸ I)) ≃ₐ[k] (J → k)) :=
  v5ComponentCoverSplitFromOwnChart e (Ideal.Quotient.mkₐ k I) Δ hρ fixed

theorem v5_canonicalComponentCover_finite_flat_unramified [Module.FaithfullyFlat B R]
    {J : Type u} [Finite J] (ρ : R →ₐ[B] R ⊗[k] H) (I : Ideal H)
    (e : R ⊗[B] v5CanonicalComponentCover ρ I ≃ₐ[R] (J → R)) :
    Module.Finite B (v5CanonicalComponentCover ρ I) ∧
      Module.Flat B (v5CanonicalComponentCover ρ I) ∧
      Algebra.Unramified B (v5CanonicalComponentCover ρ I) :=
  v5_componentCover_finite_flat_unramified ρ (Ideal.Quotient.mkₐ k I) e

end StrictEUnit
#print axioms StrictEUnit.v5_ownChart_tmul_smul
#print axioms StrictEUnit.v5ComponentCoverSplitFromOwnChart
#print axioms StrictEUnit.v5CanonicalComponentCover
#print axioms StrictEUnit.v5CanonicalComponentCoverMark
#print axioms StrictEUnit.v5CanonicalComponentCoverSplit
#print axioms StrictEUnit.v5_canonicalComponentCover_finite_flat_unramified
