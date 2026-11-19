import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! Pure finite first-dependence extraction. No differential structure is assumed.
This file is a source-only candidate, not a checked theorem artifact. -/

open scoped BigOperators

namespace FirstDependence

variable {B V : Type*} [Field B] [AddCommGroup V] [Module B V]

/-- A dependent initial segment has a first dependent vector and an independent prefix. -/
theorem exists_independent_prefix_of_dependent (v : ℕ → V) (m : ℕ)
    (hdep : ¬ LinearIndependent B (fun i : Fin (m + 1) => v i.val)) :
    ∃ r ≤ m, LinearIndependent B (fun i : Fin r => v i.val) ∧
      v r ∈ Submodule.span B (Set.range (fun i : Fin r => v i.val)) := by
  classical
  have hstep (n : ℕ) :
      LinearIndependent B (fun i : Fin (n + 1) => v i.val) ↔
        LinearIndependent B (fun i : Fin n => v i.val) ∧
          v n ∉ Submodule.span B (Set.range (fun i : Fin n => v i.val)) := by
    exact linearIndependent_fin_succ'
  induction m with
  | zero =>
      refine ⟨0, le_rfl, linearIndependent_empty_type, ?_⟩
      by_contra hnot
      exact hdep ((hstep 0).2 ⟨linearIndependent_empty_type, hnot⟩)
  | succ m ih =>
      by_cases hprefix : LinearIndependent B (fun i : Fin (m + 1) => v i.val)
      · refine ⟨m + 1, le_rfl, hprefix, ?_⟩
        by_contra hnot
        exact hdep ((hstep (m + 1)).2 ⟨hprefix, hnot⟩)
      · obtain ⟨r, hr, hli, hmem⟩ := ih hprefix
        exact ⟨r, Nat.le_trans hr (Nat.le_succ m), hli, hmem⟩

/-- A supplied nontrivial relation determines a minimal initial span and unique coordinates. -/
theorem exists_first_dependence (v : ℕ → V) (m : ℕ)
    (c : Fin (m + 1) → B) (hc : ∃ i, c i ≠ 0)
    (hrel : ∑ i, c i • v i.val = 0) :
    ∃ r ≤ m, LinearIndependent B (fun i : Fin r => v i.val) ∧
      v r ∈ Submodule.span B (Set.range (fun i : Fin r => v i.val)) ∧
      ∃! b : Fin r → B, ∑ i, b i • v i.val = v r := by
  classical
  have hdep : ¬ LinearIndependent B (fun i : Fin (m + 1) => v i.val) :=
    Fintype.not_linearIndependent_iff.2 ⟨c, hrel, hc⟩
  obtain ⟨r, hr, hli, hmem⟩ := exists_independent_prefix_of_dependent v m hdep
  refine ⟨r, hr, hli, hmem, ?_⟩
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun B).1 hmem
  refine ⟨b, hb, ?_⟩
  intro b' hb'
  apply hli.fintypeLinearCombination_injective
  simpa only [Fintype.linearCombination_apply] using hb'.trans hb.symm

/-- A first dependence at index zero is precisely the zero-vector case. -/
theorem first_dependence_zero_iff (v : ℕ → V) (r : ℕ)
    (hli : LinearIndependent B (fun i : Fin r => v i.val))
    (hmem : v r ∈ Submodule.span B (Set.range (fun i : Fin r => v i.val))) :
    r = 0 ↔ v 0 = 0 := by
  constructor
  · intro hr
    subst r
    simpa using hmem
  · intro hv
    by_contra hr
    have hpos : 0 < r := Nat.pos_of_ne_zero hr
    have hne := hli.ne_zero (⟨0, hpos⟩ : Fin r)
    exact hne hv

/-- Positive order follows from the original first vector being nonzero, not from dependence alone. -/
theorem exists_positive_first_dependence (v : ℕ → V) (hv : v 0 ≠ 0) (m : ℕ)
    (c : Fin (m + 1) → B) (hc : ∃ i, c i ≠ 0)
    (hrel : ∑ i, c i • v i.val = 0) :
    ∃ r, 0 < r ∧ r ≤ m ∧
      LinearIndependent B (fun i : Fin r => v i.val) ∧
      v r ∈ Submodule.span B (Set.range (fun i : Fin r => v i.val)) ∧
      ∃! b : Fin r → B, ∑ i, b i • v i.val = v r := by
  obtain ⟨r, hr, hli, hmem, hcoords⟩ := exists_first_dependence v m c hc hrel
  refine ⟨r, Nat.pos_of_ne_zero ?_, hr, hli, hmem, hcoords⟩
  intro hz
  exact hv ((first_dependence_zero_iff v r hli hmem).1 hz)

end FirstDependence
