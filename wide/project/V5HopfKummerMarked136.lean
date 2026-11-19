import V5HopfKummerReciprocal136
import V5MarkedTensorUniqueness136
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
universe u v t l
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k : Type t} {B : Type v} {R H : Type u} {L : Type l} {W C : Type*}
  [Field k] [IsAlgClosed k] [CommRing B] [CommRing R] [CommRing H]
  [HopfAlgebra k H] [Algebra.FiniteType k H] [IsReduced H]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
  [CommRing L] [IsDomain L] [IsPrincipalIdealRing L] [Algebra k L]
  [CommRing W] [Algebra k W] [Algebra B W] [IsScalarTower k B W]
  [CommRing C] [Algebra k C]
def v5HopfKummerMarked136 [Module.FaithfullyFlat B R]
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) (ρ : R →ₐ[B] R ⊗[k] H)
    (he : ∀ r s, e.symm (r ⊗ₜ[B] s) = r • ρ s)
    (hρ : ∀ r, Algebra.TensorProduct.assoc k R H H
      (Algebra.TensorProduct.map (ρ.restrictScalars k) (AlgHom.id k H) (ρ r)) =
      Algebra.TensorProduct.map (AlgHom.id R R) (Bialgebra.comulAlgHom k H) (ρ r))
    (s : H →ₐ[k] H) (hs : s.toLinearMap = HopfAlgebra.antipode)
    (I : Ideal H) (hmin : I ∈ minimalPrimes H)
    (hI : I ≤ RingHom.ker (Bialgebra.counitAlgHom k H).toRingHom)
    (hu : ∀ P ∈ minimalPrimes H,
      P ≤ RingHom.ker (Bialgebra.counitAlgHom k H).toRingHom → P = I)
    (α : v5CanonicalComponentCover ρ I →ₐ[k] L)
    (pL : L →ₐ[k] k) (pR : R →ₐ[k] k)
    (hm : ∀ t : v5CanonicalComponentCover ρ I, pL (α t) = pR (t : R))
    (pW : W →ₐ[k] C)
    (pM : R ⊗[B] W →ₐ[k] C)
    (ht : ∀ r w, pM (r ⊗ₜ[B] w) = algebraMap k C (pR r) * pW w)
    (u : (R ⊗[B] W)ˣ) (a c : C)
    (hvalue : pM (u : R ⊗[B] W) = a)
    (hinv : pM (↑u⁻¹ : R ⊗[B] W) = c) := by
  let hR := v5MarkedTensorBaseCompatibility136 pR pW pM ht
  have hp := v5MarkedTensorEq135136 pR pW pM ht
  have hval : v5MixedMarkedTensor135 pR pW hR (u : R ⊗[B] W) = a := by
    rw [← hp]
    exact hvalue
  have hiv : v5MixedMarkedTensor135 pR pW hR (↑u⁻¹ : R ⊗[B] W) = c := by
    rw [← hp]
    exact hinv
  exact v5HopfKummerReciprocal136 e ρ he hρ s hs I hmin hI hu α pL pR hm
    pW hR u a c hval hiv
end StrictEUnit
#print axioms StrictEUnit.v5HopfKummerMarked136
