import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Quotient.Basic

/-! Projectivity of the actual quotient by a copy of the base yields a
linear unit retraction. No differential-module projectivity is assumed
proved by this construction. -/
noncomputable section
namespace StrictEUnit
section Split
variable {B M P : Type*} [CommRing B] [AddCommGroup M] [AddCommGroup P]
  [Module B M] [Module B P]

/-- A projective cokernel splits any injective linear inclusion. -/
theorem retraction_of_projective_quotient (f : M →ₗ[B] P)
    (hf : Function.Injective f) [Module.Projective B (P ⧸ LinearMap.range f)] :
    ∃ π : P →ₗ[B] M, π.comp f = LinearMap.id := by
  let N := LinearMap.range f
  obtain ⟨s, hs⟩ := N.mkQ.exists_rightInverse_of_surjective N.range_mkQ
  let t : P →ₗ[B] P := LinearMap.id - s.comp N.mkQ
  have ht : ∀ p, t p ∈ N := by
    intro p
    rw [← Submodule.ker_mkQ N, LinearMap.mem_ker]
    change N.mkQ (p - s (N.mkQ p)) = 0
    rw [map_sub, show N.mkQ (s (N.mkQ p)) = N.mkQ p from
      LinearMap.congr_fun hs (N.mkQ p), sub_self]
  let e : M ≃ₗ[B] N := LinearEquiv.ofInjective f hf
  let π : P →ₗ[B] M := e.symm.toLinearMap.comp (t.codRestrict N ht)
  refine ⟨π, ?_⟩
  apply LinearMap.ext
  intro m
  apply e.injective
  change e (e.symm ⟨t (f m), ht (f m)⟩) = e m
  rw [e.apply_symm_apply]
  apply Subtype.ext
  change f m - s (N.mkQ (f m)) = f m
  have hz : N.mkQ (f m) = 0 := by
    apply LinearMap.mem_ker.mp
    rw [Submodule.ker_mkQ]
    exact ⟨m, rfl⟩
  rw [hz, map_zero, sub_zero]
end Split

section Unit
variable {B R : Type*} [CommRing B] [CommRing R] [Algebra B R]

/-- The actual base inclusion into a submodule containing one. -/
def submoduleUnitInclusion (P : Submodule B R) (h1 : (1 : R) ∈ P) : B →ₗ[B] P :=
  (Algebra.linearMap B R).codRestrict P (by
    intro b
    simpa only [Algebra.smul_def, mul_one] using P.smul_mem b h1)

@[simp] theorem submoduleUnitInclusion_coe
    (P : Submodule B R) (h1 : (1 : R) ∈ P) (b : B) :
    (submoduleUnitInclusion P h1 b : R) = algebraMap B R b := rfl

/-- The quotient is by the actual embedded copy of B, not a replacement
module with an assumed retraction. -/
theorem unit_retraction_of_projective_quotient
    (hinj : Function.Injective (algebraMap B R))
    (P : Submodule B R) (h1 : (1 : R) ∈ P)
    [Module.Projective B (P ⧸ LinearMap.range (submoduleUnitInclusion P h1))] :
    ∃ π : P →ₗ[B] B, π ⟨1, h1⟩ = 1 := by
  have hf : Function.Injective (submoduleUnitInclusion P h1) := by
    intro b c h
    exact hinj (congrArg Subtype.val h)
  obtain ⟨π, hπ⟩ := retraction_of_projective_quotient (submoduleUnitInclusion P h1) hf
  refine ⟨π, ?_⟩
  have h := LinearMap.congr_fun hπ (1 : B)
  have hone : submoduleUnitInclusion P h1 (1 : B) = ⟨1, h1⟩ := by
    apply Subtype.ext
    exact map_one (algebraMap B R)
  simpa only [LinearMap.comp_apply, LinearMap.id_apply, hone] using h
end Unit
end StrictEUnit

#print axioms StrictEUnit.retraction_of_projective_quotient
#print axioms StrictEUnit.submoduleUnitInclusion
#print axioms StrictEUnit.submoduleUnitInclusion_coe
#print axioms StrictEUnit.unit_retraction_of_projective_quotient
