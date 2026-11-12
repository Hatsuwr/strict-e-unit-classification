import FlatFromFinitePieces
import SplitUnitRetraction
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! Faithfulness requires more than flatness. This criterion supplies it from
actual finite-piece linear retractions preserving the unit. It does not assert
that the differential pieces of a particular PV candidate have such retractions. -/
noncomputable section
namespace StrictEUnit
variable {B R : Type*} [CommRing B] [CommRing R] [Algebra B R]

/-- Finite-piece retractions preserving 1 prevent a proper base ideal from
extending to the unit ideal. Together with flatness this gives faithful flatness. -/
theorem faithfullyFlat_of_finite_unit_retractions [Module.Flat B R]
    (hpieces : ∀ s : Finset R, ∃ P : Submodule B R, ∃ h1 : (1 : R) ∈ P,
      ∃ π : P →ₗ[B] B, π ⟨1, h1⟩ = 1 ∧ ∀ r ∈ s, r ∈ P) :
    Module.FaithfullyFlat B R := by
  apply (Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top B R).mpr
  refine ⟨inferInstance, ?_⟩
  intro I hI
  have hmem : (1 : R) ∈ I • Submodule.span B (Set.range (id : R → R)) := by
    simpa only [Set.range_id, Submodule.span_univ, hI] using
      (Submodule.mem_top : (1 : R) ∈ (⊤ : Submodule B R))
  obtain ⟨a, ha, hsum⟩ :=
    (Submodule.mem_ideal_smul_span_iff_exists_sum I (id : R → R) 1).mp hmem
  obtain ⟨P, h1, π, hπ, hP⟩ := hpieces a.support
  let y : a.support → P := fun i => ⟨(i : R), hP i i.property⟩
  have hsumP : ∑ i : a.support, a (i : R) • y i = ⟨1, h1⟩ := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, y]
    exact (Finset.sum_coe_sort a.support (fun r : R => a r • r)).trans hsum
  have he := congrArg π hsumP
  simp only [map_sum, map_smul, smul_eq_mul, hπ] at he
  apply Ideal.eq_top_of_isUnit_mem I (x := (1 : B))
  · rw [← he]
    exact I.sum_mem fun i _ => I.mul_mem_right _ (ha (i : R))
  · exact isUnit_one

/-- Projective finite pieces with such actual retractions give both flatness
and faithfulness. Projectivity and retractions remain explicit inputs. -/
theorem faithfullyFlat_of_projective_split_pieces
    (hpieces : ∀ s : Finset R, ∃ P : Submodule B R,
      Module.Projective B P ∧ ∃ h1 : (1 : R) ∈ P,
      ∃ π : P →ₗ[B] B, π ⟨1, h1⟩ = 1 ∧ ∀ r ∈ s, r ∈ P) :
    Module.FaithfullyFlat B R := by
  classical
  have hflat : Module.Flat B R := by
    apply flat_of_finite_families_in_projective_submodules
    intro l x
    obtain ⟨P, hp, h1, π, hπ, hx⟩ := hpieces (Finset.univ.image x)
    exact ⟨P, hp, fun i => hx (x i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)⟩
  letI := hflat
  apply faithfullyFlat_of_finite_unit_retractions
  intro s
  obtain ⟨P, hp, h1, π, hπ, hx⟩ := hpieces s
  exact ⟨P, h1, π, hπ, hx⟩
/-- Actual projectivity of the pieces and their quotients by B produces the
required retractions, and hence faithful flatness. -/
theorem faithfullyFlat_of_projective_pieces_and_quotients
    (hinj : Function.Injective (algebraMap B R))
    (hpieces : ∀ s : Finset R, ∃ P : Submodule B R,
      Module.Projective B P ∧ ∃ h1 : (1 : R) ∈ P,
      Module.Projective B (P ⧸ LinearMap.range (submoduleUnitInclusion P h1)) ∧
      ∀ r ∈ s, r ∈ P) : Module.FaithfullyFlat B R := by
  apply faithfullyFlat_of_projective_split_pieces
  intro s
  obtain ⟨P, hp, h1, hq, hs⟩ := hpieces s
  letI := hq
  obtain ⟨π, hπ⟩ := unit_retraction_of_projective_quotient hinj P h1
  exact ⟨P, hp, h1, π, hπ, hs⟩

end StrictEUnit
#print axioms StrictEUnit.faithfullyFlat_of_finite_unit_retractions
#print axioms StrictEUnit.faithfullyFlat_of_projective_split_pieces

#print axioms StrictEUnit.faithfullyFlat_of_projective_pieces_and_quotients
