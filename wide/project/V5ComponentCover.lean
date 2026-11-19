import V5SplitEqualizerDescent
import Mathlib.RingTheory.TensorProduct.Basic

noncomputable section
open scoped TensorProduct
namespace StrictEUnit
universe u v w w' l
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule

variable {B : Type v} {k : Type w} {R : Type u} {H : Type w'} {N : Type l}
  [CommRing B] [Field k] [CommRing R] [CommRing H] [CommRing N]
  [Algebra B R] [Algebra k B] [Algebra k R] [IsScalarTower k B R] [Algebra k H] [Algebra k N]

/-- The restricted own action uses the actual quotient on the constant factor. -/
def v5ComponentOwnAction (ρ : R →ₐ[B] R ⊗[k] H) (q : H →ₐ[k] N) :
    R →ₐ[B] R ⊗[k] N :=
  (Algebra.TensorProduct.map (AlgHom.id B R) q).comp ρ

def v5ComponentOwnTrivial : R →ₐ[B] R ⊗[k] N :=
  Algebra.TensorProduct.includeLeft

/-- The invariant ring over the Laurent base, defined as a genuine algebra equalizer. -/
def v5ComponentCoverAlgebra (ρ : R →ₐ[B] R ⊗[k] H) (q : H →ₐ[k] N) : Subalgebra B R :=
  AlgHom.equalizer (v5ComponentOwnAction ρ q) v5ComponentOwnTrivial

/-- The point of R over the chosen base point restricts to the invariant ring. -/
def v5ComponentCoverMark
    (ρ : R →ₐ[B] R ⊗[k] H) (q : H →ₐ[k] N) (p : R →ₐ[k] k) :
    v5ComponentCoverAlgebra ρ q →ₐ[k] k :=
  p.comp ((v5ComponentCoverAlgebra ρ q).val.restrictScalars k)

@[simp] theorem v5ComponentCoverMark_apply
    (ρ : R →ₐ[B] R ⊗[k] H) (q : H →ₐ[k] N) (p : R →ₐ[k] k)
    (x : v5ComponentCoverAlgebra ρ q) :
    v5ComponentCoverMark ρ q p x = p x.val := rfl

/-- Once the own torsor and its two action squares are checked, the invariant
ring is split by the very same faithfully flat candidate R. -/
def v5ComponentCoverSplit [Module.Flat B R] {J : Type u} [Finite J]
    (ρ : R →ₐ[B] R ⊗[k] H) (q : H →ₐ[k] N) (δ : H →ₐ[k] H ⊗[k] N)
    (e : R ⊗[B] R ≃ₐ[R] R ⊗[k] H) (E : R ⊗[B] (R ⊗[k] N) ≃ₐ[R] R ⊗[k] (H ⊗[k] N))
    (hρ : ∀ x, E (Algebra.TensorProduct.map (AlgHom.id R R) (v5ComponentOwnAction ρ q) x) =
      Algebra.TensorProduct.map (AlgHom.id R R) δ (e x))
    (hι : ∀ x, E (Algebra.TensorProduct.map (AlgHom.id R R) v5ComponentOwnTrivial x) =
      Algebra.TensorProduct.map (AlgHom.id R R) (Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] N) (e x))
    (fixed : AlgHom.equalizer δ (Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] N) ≃ₐ[k] (J → k)) :
    R ⊗[B] v5ComponentCoverAlgebra ρ q ≃ₐ[R] (J → R) :=
  v5SplitEqualizerBaseChange (v5ComponentOwnAction ρ q) v5ComponentOwnTrivial δ _
    e E hρ hι fixed

theorem v5_componentCover_finite_flat_unramified [Module.FaithfullyFlat B R]
    {J : Type u} [Finite J] (ρ : R →ₐ[B] R ⊗[k] H) (q : H →ₐ[k] N)
    (e : R ⊗[B] v5ComponentCoverAlgebra ρ q ≃ₐ[R] (J → R)) :
    Module.Finite B (v5ComponentCoverAlgebra ρ q) ∧ Module.Flat B (v5ComponentCoverAlgebra ρ q) ∧
      Algebra.Unramified B (v5ComponentCoverAlgebra ρ q) :=
  v5_split_equalizer_descent (v5ComponentOwnAction ρ q) v5ComponentOwnTrivial e

end StrictEUnit
#print axioms StrictEUnit.v5ComponentOwnAction
#print axioms StrictEUnit.v5ComponentCoverAlgebra
#print axioms StrictEUnit.v5ComponentCoverMark_apply
#print axioms StrictEUnit.v5ComponentCoverSplit
#print axioms StrictEUnit.v5_componentCover_finite_flat_unramified
