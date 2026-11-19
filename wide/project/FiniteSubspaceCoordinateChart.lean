import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.StdBasis

/-!
A coordinate chart for an arbitrary subspace of a finite coordinate space.
The pivot coordinates are selected from the actual coordinate functionals.
No chart, independent family, prescribed dimension or nonzero subspace is
assumed. This module has no derivative, Laurent or constant-descent premise.
-/
noncomputable section
namespace StrictEUnit
variable {F : Type*} [Field F] {r : ℕ}

/-- Restrict an ambient coordinate functional to the SAME subspace. -/
def subspaceCoordinateForm (E : Submodule F (Fin r → F)) (i : Fin r) :
    Module.Dual F E :=
  (LinearMap.proj i).comp E.subtype

@[simp] theorem subspaceCoordinateForm_apply
    (E : Submodule F (Fin r → F)) (i : Fin r) (v : E) :
    subspaceCoordinateForm E i v = (v : Fin r → F) i := rfl

/-- Actual coordinate separation proves that these restricted functionals
span the dual. Finite dimensionality is inherited from the finite ambient space. -/
theorem subspaceCoordinateForms_span (E : Submodule F (Fin r → F)) :
    Submodule.span F (Set.range (subspaceCoordinateForm E)) = ⊤ := by
  classical
  apply Submodule.span_eq_top_of_ne_zero
  intro v hv
  have hne : (v : Fin r → F) ≠ 0 := by
    intro h
    exact hv (Subtype.ext h)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  exact ⟨subspaceCoordinateForm E i, Set.mem_range_self i, hi⟩

/-- A selected coordinate projection is a linear equivalence. The number of
pivots and their injection are derived, including E=0 and r=0. -/
theorem exists_subspace_coordinate_chart (E : Submodule F (Fin r → F)) :
    ∃ s : ℕ, s ≤ r ∧ ∃ p : Fin s ↪ Fin r,
      ∃ e : E ≃ₗ[F] (Fin s → F),
        ∀ v : E, ∀ i : Fin s, e v i = (v : Fin r → F) (p i) := by
  classical
  let c : Fin r → Module.Dual F E := subspaceCoordinateForm E
  letI : Module.Finite F (Submodule.span F (Set.range c)) :=
    Module.Finite.span_of_finite F (Set.finite_range c)
  let s := Module.finrank F (Submodule.span F (Set.range c))
  obtain ⟨g, hgmem, hgspan, hgli⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq F (Set.range c)
  choose p hp using (fun i : Fin s => hgmem i)
  have hpinj : Function.Injective p := by
    intro i j hij
    apply hgli.injective
    rw [← hp i, ← hp j, hij]
  have hs : s ≤ r := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective p hpinj
  have hsp : (⊤ : Submodule F (Module.Dual F E)) ≤
      Submodule.span F (Set.range g) := by
    rw [hgspan]
    exact (subspaceCoordinateForms_span E).ge
  let b : Basis (Fin s) F (Module.Dual F E) := Basis.mk hgli hsp
  have hb (i : Fin s) : b i = g i := Basis.mk_apply hgli hsp i
  let e : E ≃ₗ[F] (Fin s → F) :=
    (Module.evalEquiv F E).trans b.dualBasis.equivFun
  refine ⟨s, hs, ⟨p, hpinj⟩, e, ?_⟩
  intro v i
  change b.dualBasis.equivFun ((Module.evalEquiv F E) v) i = _
  rw [Basis.dualBasis_equivFun, Module.evalEquiv_apply, Module.Dual.eval_apply,
    hb, ← hp i]
  rfl

/-- The chart yields an actual basis with identity pivot rows and ambient
span exactly E. Its size is the actual finrank, not a supplied parameter. -/
theorem exists_normalized_subspace_coordinate_basis
    (E : Submodule F (Fin r → F)) :
    ∃ s : ℕ, s ≤ r ∧ s = Module.finrank F E ∧
      ∃ p : Fin s ↪ Fin r, ∃ e : E ≃ₗ[F] (Fin s → F),
        ∃ b : Basis (Fin s) F E,
          (∀ v : E, ∀ i : Fin s, e v i = (v : Fin r → F) (p i)) ∧
          (∀ j : Fin s, e (b j) = (Pi.basisFun F (Fin s)) j) ∧
          (∀ i j : Fin s, (b j : Fin r → F) (p i) = if i = j then 1 else 0) ∧
          Submodule.span F (Set.range (fun j : Fin s => (b j : Fin r → F))) = E := by
  classical
  obtain ⟨s, hs, p, e, he⟩ := exists_subspace_coordinate_chart E
  let b : Basis (Fin s) F E := (Pi.basisFun F (Fin s)).map e.symm
  have hbe (j : Fin s) : e (b j) = (Pi.basisFun F (Fin s)) j := by
    change e (((Pi.basisFun F (Fin s)).map e.symm) j) = _
    rw [Basis.map_apply, LinearEquiv.apply_symm_apply]
  have hdim : s = Module.finrank F E := by
    simpa only [Fintype.card_fin] using (Module.finrank_eq_card_basis b).symm
  refine ⟨s, hs, hdim, p, e, b, he, hbe, ?_, ?_⟩
  · intro i j
    rw [← he (b j) i, hbe]
    by_cases hij : i = j <;> simp [Pi.basisFun_apply, hij]
  · change Submodule.span F (Set.range (E.subtype ∘ b)) = E
    rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]

end StrictEUnit
end
