import Mathlib.RingTheory.Flat.EquationalCriterion

/-! A concrete finite-piece criterion for flatness. This proves the final
union step of a filtration argument, but does not prove that the finite
differential pieces arising in a PV construction are projective. -/
noncomputable section
namespace StrictEUnit
variable {B M : Type*} [CommRing B] [AddCommGroup M] [Module B M]

/-- Flatness follows if every finite family lies in a flat submodule. -/
theorem flat_of_finite_families_in_flat_submodules
    (hpieces : ∀ (l : ℕ) (x : Fin l → M),
      ∃ N : Submodule B M, Module.Flat B N ∧ ∀ i, x i ∈ N) :
    Module.Flat B M := by
  apply Module.Flat.of_forall_isTrivialRelation
  intro l f x hrel
  obtain ⟨N, hN, hx⟩ := hpieces l x
  letI : Module.Flat B N := hN
  let y : Fin l → N := fun i => ⟨x i, hx i⟩
  have hrelN : ∑ i, f i • y i = 0 := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower, y,
      Submodule.coe_zero] using hrel
  obtain ⟨j, a, z, hfactor, hzero⟩ :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrelN
  refine ⟨j, a, fun i => (z i : M), ?_, hzero⟩
  intro i
  have hh := congrArg (fun n : N => (n : M)) (hfactor i)
  simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower, y] using hh

/-- In particular, finite projective pieces suffice; no colimit framework
or global freeness assumption is needed. -/
theorem flat_of_finite_families_in_projective_submodules
    (hpieces : ∀ (l : ℕ) (x : Fin l → M),
      ∃ N : Submodule B M, Module.Projective B N ∧ ∀ i, x i ∈ N) :
    Module.Flat B M := by
  apply flat_of_finite_families_in_flat_submodules
  intro l x
  obtain ⟨N, hN, hx⟩ := hpieces l x
  letI : Module.Projective B N := hN
  exact ⟨N, inferInstance, hx⟩
end StrictEUnit

#print axioms StrictEUnit.flat_of_finite_families_in_flat_submodules
#print axioms StrictEUnit.flat_of_finite_families_in_projective_submodules
