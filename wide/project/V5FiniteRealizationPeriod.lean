import V5IntegralAutomorphismPeriod
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.FiniteType

noncomputable section
namespace StrictEUnit

def v5AlgEquivRingMonoid (B A : Type*) [CommSemiring B] [Semiring A] [Algebra B A] :
    (A ≃ₐ[B] A) →* (A ≃+* A) where
  toFun := AlgEquiv.toRingEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

theorem v5AlgEquivRingMonoid_pow {B A : Type*} [CommSemiring B] [Semiring A] [Algebra B A]
    (s : A ≃ₐ[B] A) (q : ℕ) : (s ^ q).toRingEquiv = s.toRingEquiv ^ q :=
  map_pow (v5AlgEquivRingMonoid B A) s q

/-- A finite algebra realized in a domain acquires one common positive
period under an automorphism fixing the realized base. The realization itself
need not be injective, and the ambient automorphism need not preserve it a priori. -/
theorem v5_common_period_of_finite_realization {B T A : Type*}
    [CommRing B] [CommRing T] [CommRing A] [IsDomain A]
    [Algebra B T] [Module.Finite B T] (ρ : T →+* A) (σ : A ≃+* A)
    (hσ : ∀ b : B, σ (ρ (algebraMap B T b)) = ρ (algebraMap B T b)) :
    ∃ q : ℕ, 0 < q ∧ ∀ t, (σ ^ q) (ρ t) = ρ t := by
  letI : Algebra B A := (ρ.comp (algebraMap B T)).toAlgebra
  let r : T →ₐ[B] A := {toRingHom := ρ, commutes' := fun _ => rfl}
  let s : A ≃ₐ[B] A := AlgEquiv.ofRingEquiv (f := σ) hσ
  have hfg : r.range.FG := (Subalgebra.fg_iff_finiteType r.range).mpr
    (Algebra.FiniteType.of_surjective inferInstance r.rangeRestrict r.rangeRestrict_surjective)
  have hi : ∀ x ∈ r.range, IsIntegral B x := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨p, hp, ht⟩ := IsIntegral.of_finite B t
    refine ⟨p, hp, ?_⟩
    change Polynomial.aeval (r t) p = 0
    change Polynomial.aeval t p = 0 at ht
    rw [Polynomial.aeval_algHom_apply, ht, map_zero]
  obtain ⟨q, hq, h⟩ := v5_integral_fg_subalgebra_common_period s r.range hfg hi
  refine ⟨q, hq, fun t => ?_⟩
  have ht := h (r t) ⟨t, rfl⟩
  have hs := v5AlgEquivRingMonoid_pow s q
  change (s ^ q).toRingEquiv = σ ^ q at hs
  rw [← hs]
  exact ht

end StrictEUnit
#print axioms StrictEUnit.v5_common_period_of_finite_realization
