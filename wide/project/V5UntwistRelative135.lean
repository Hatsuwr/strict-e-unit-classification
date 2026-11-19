import V5HopfRelativeAssembly134
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k B T R H N J : Type*}
  [Field k] [CommRing B] [CommRing T] [CommRing R] [CommRing H] [CommRing N]
  [Algebra k R] [Algebra k H] [Algebra k N]
  [Algebra k B] [Algebra B R] [IsScalarTower k B R] [Algebra T R] [Fintype J] [DecidableEq J]
theorem v5UntwistRelative135
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R)
    (ρ : R →ₐ[B] R ⊗[k] H) (q : H →ₐ[k] N)
    (he : ∀ a b, e.symm (a ⊗ₜ[B] b) = a • ρ b)
    (C : H ≃ₐ[k] (J → N)) (i : J) (u : N ≃ₐ[k] N)
    (hc : ∀ h, C h i = u (q h))
    (rel : R ⊗[T] R ≃ₐ[R] R ⊗[k] N)
    (hrel : ∀ a b, rel (a ⊗ₜ[T] b) =
      (e.symm.trans (v5TensorComponentChart132 C)) (a ⊗ₜ[B] b) i) :
    ∃ natural : R ⊗[T] R ≃ₐ[R] R ⊗[k] N, ∀ a b,
      natural (a ⊗ₜ[T] b) =
        a • Algebra.TensorProduct.map (AlgHom.id R R) q (ρ b) := by
  let F : R ⊗[k] N ≃ₐ[R] R ⊗[k] N :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) u.symm
  have hinv (z : R ⊗[k] N) :
      F (Algebra.TensorProduct.map (AlgHom.id R R) u.toAlgHom z) = z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r n =>
      change r ⊗ₜ[k] u.symm (u n) = r ⊗ₜ[k] n
      rw [u.symm_apply_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hcoord (z : R ⊗[k] H) :
      v5TensorComponentChart132 C z i =
        Algebra.TensorProduct.map (AlgHom.id R R) u.toAlgHom
          (Algebra.TensorProduct.map (AlgHom.id R R) q z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r h =>
      change r ⊗ₜ[k] C h i = r ⊗ₜ[k] u (q h)
      rw [hc]
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  refine ⟨rel.trans F, ?_⟩
  intro a b
  change F (rel (a ⊗ₜ[T] b)) = _
  rw [hrel]
  change F (v5TensorComponentChart132 C (e.symm (a ⊗ₜ[B] b)) i) = _
  rw [hcoord, hinv, he, map_smul]
end StrictEUnit
#print axioms StrictEUnit.v5UntwistRelative135
