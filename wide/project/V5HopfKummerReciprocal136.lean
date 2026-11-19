import V5KummerReciprocalValues136
import V5ApplyAmbientCharacter136
import V5NaturalHopfRelative135
import V5CoverRestrictedCoaction135
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
def v5HopfKummerReciprocal136 [Module.FaithfullyFlat B R]
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
    (hR : ∀ b, algebraMap k C (pR (algebraMap B R b)) = pW (algebraMap B W b))
    (u : (R ⊗[B] W)ˣ) (a c : C)
    (hvalue : v5MixedMarkedTensor135 pR pW hR (u : R ⊗[B] W) = a)
    (hinv : v5MixedMarkedTensor135 pR pW hR (↑u⁻¹ : R ⊗[B] W) = c) :
  letI : I.IsPrime := Ideal.minimalPrimes_isPrime hmin
  letI := v5_primeQuotient_tensorSquare_isDomain (k := k) I
  let ε := v5ComponentCounit I (Bialgebra.counitAlgHom k H) hI
  let Δ := v5ComponentCoproduct I (Bialgebra.counitAlgHom k H) hI hu
    (Bialgebra.comulAlgHom k H) (v5_hopfComponent_doubleCounit (k := k))
  let assembly := v5NaturalHopfRelative135 e ρ he hρ s hs I hmin hI hu
  letI := assembly.1
  let τ := v5CoverRestrictedCoaction135 ρ I
  letI : IsScalarTower k (v5CanonicalComponentCover ρ I) R :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      (((v5CanonicalComponentCover ρ I).val.restrictScalars k).commutes x).symm)
  letI : Algebra (v5CanonicalComponentCover ρ I) L := α.toAlgebra
  letI : IsScalarTower k (v5CanonicalComponentCover ρ I) L :=
    IsScalarTower.of_algebraMap_eq (fun x => (α.commutes x).symm)
  letI : Algebra B L := (α.toRingHom.comp (algebraMap B (v5CanonicalComponentCover ρ I))).toAlgebra
  letI : IsScalarTower B (v5CanonicalComponentCover ρ I) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower k B L := IsScalarTower.of_algebraMap_eq (fun x => by
    change algebraMap k L x = α (algebraMap B (v5CanonicalComponentCover ρ I) (algebraMap k B x))
    rw [← IsScalarTower.algebraMap_apply k B (v5CanonicalComponentCover ρ I), α.commutes])
  (∃ χ : (H ⧸ I)ˣ,
      v5MixedRelativeCoaction (S := W) (τ.restrictScalars B) (u : R ⊗[B] W) =
        (u : R ⊗[B] W) ⊗ₜ[k] (χ : H ⧸ I) ∧
      ε (χ : H ⧸ I) = 1 ∧ Δ (χ : H ⧸ I) = (χ : H ⧸ I) ⊗ₜ[k] (χ : H ⧸ I)) →
    ∃ χ : (H ⧸ I)ˣ, V5KummerLiftResult136 τ pL pR pW hm hR u a c χ := by
  classical
  letI : I.IsPrime := Ideal.minimalPrimes_isPrime hmin
  letI := v5_primeQuotient_tensorSquare_isDomain (k := k) I
  let ε := v5ComponentCounit I (Bialgebra.counitAlgHom k H) hI
  let Δ := v5ComponentCoproduct I (Bialgebra.counitAlgHom k H) hI hu
    (Bialgebra.comulAlgHom k H) (v5_hopfComponent_doubleCounit (k := k))
  let assembly := v5NaturalHopfRelative135 e ρ he hρ s hs I hmin hI hu
  letI := assembly.1
  let rel := Classical.choose assembly.2
  let hrel := Classical.choose_spec assembly.2
  let τ := v5CoverRestrictedCoaction135 ρ I
  letI : IsScalarTower k (v5CanonicalComponentCover ρ I) R :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      (((v5CanonicalComponentCover ρ I).val.restrictScalars k).commutes x).symm)
  letI : Algebra (v5CanonicalComponentCover ρ I) L := α.toAlgebra
  letI : IsScalarTower k (v5CanonicalComponentCover ρ I) L :=
    IsScalarTower.of_algebraMap_eq (fun x => (α.commutes x).symm)
  letI : Algebra B L := (α.toRingHom.comp (algebraMap B (v5CanonicalComponentCover ρ I))).toAlgebra
  letI : IsScalarTower B (v5CanonicalComponentCover ρ I) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower k B L := IsScalarTower.of_algebraMap_eq (fun x => by
    change algebraMap k L x = α (algebraMap B (v5CanonicalComponentCover ρ I) (algebraMap k B x))
    rw [← IsScalarTower.algebraMap_apply k B (v5CanonicalComponentCover ρ I), α.commutes])
  let hc := v5RestrictedCoassoc135 ρ (Ideal.Quotient.mkₐ k I)
    (Bialgebra.comulAlgHom k H) Δ (fun _ => rfl) hρ
  exact v5ApplyAmbientCharacter136 (k := k) (M := R ⊗[B] W) (N := H ⧸ I)
    (δ := v5MixedRelativeCoaction (S := W) (τ.restrictScalars B)) (Δ := Δ) (ε := ε) (u := u)
    (P := fun χ => V5KummerLiftResult136 τ pL pR pW hm hR u a c χ)
    (v5KummerReciprocalValues136 (L := L) Δ ε
      (v5_component_leftCounit_of_surjective (Ideal.Quotient.mkₐ k I)
        (Ideal.Quotient.mkₐ_surjective k I) ε Δ (fun _ => rfl) (fun _ => rfl))
      τ rel hrel hc pL pR pW hm hR u a c hvalue hinv)
end StrictEUnit
#print axioms StrictEUnit.v5HopfKummerReciprocal136
