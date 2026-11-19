import DifferentialFiniteFiltration
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Finite differential spans and scalar relations

This module constructs finite differential-stable subspaces for sums and products
and extracts a nonzero scalar linear differential relation by finite-dimensional
linear dependence. The scalar field may carry a nonzero derivation. These are
algebraic statements, not a bridge from analytic functions to a differential field.
-/
noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {k B R : Type*} [CommRing k] [Field B] [CommRing R]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]

/-- An element lies in an actual finitely generated, differential-stable scalar
subspace. Stability and finite generation are properties of the displayed subspace. -/
def HasFiniteDifferentialSpan (d : Derivation k R R) (f : R) : Prop :=
  ∃ M : Submodule B R, M.FG ∧ (∀ x ∈ M, d x ∈ M) ∧ f ∈ M

/-- A homogeneous scalar differential relation with a genuinely nonzero tuple.
The iteration is of the given derivation, not of an unspecified formal operator. -/
def HasScalarLinearDifferentialRelation (d : Derivation k R R) (f : R) : Prop :=
  ∃ n : ℕ, ∃ c : Fin (n + 1) → B,
    (∃ i, c i ≠ 0) ∧ ∑ i, c i • ((d : R → R)^[i.val]) f = 0

/-- The sum of two differential-stable subspaces is differential-stable. -/
theorem stage14_differential_sup_stable (d : Derivation k R R)
    (M N : Submodule B R)
    (hM : ∀ x ∈ M, d x ∈ M) (hN : ∀ x ∈ N, d x ∈ N) :
    ∀ x ∈ M ⊔ N, d x ∈ M ⊔ N := by
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  simpa only [map_add] using Submodule.add_mem_sup (hM y hy) (hN z hz)

/-- The actual sum subspace is a finite stable witness for the sum. -/
theorem finiteDifferentialSpan_add (d : Derivation k R R) {f g : R}
    (hf : HasFiniteDifferentialSpan (B := B) d f)
    (hg : HasFiniteDifferentialSpan (B := B) d g) :
    HasFiniteDifferentialSpan (B := B) d (f + g) := by
  obtain ⟨M, hMfg, hM, hf⟩ := hf
  obtain ⟨N, hNfg, hN, hg⟩ := hg
  exact ⟨M ⊔ N, hMfg.sup hNfg, stage14_differential_sup_stable d M N hM hN,
    Submodule.add_mem_sup hf hg⟩

/-- The subspace spanned by products of members is finite and stable by the
Leibniz rule; it contains the actual product of the input elements. -/
theorem finiteDifferentialSpan_mul (d : Derivation k R R) {f g : R}
    (hf : HasFiniteDifferentialSpan (B := B) d f)
    (hg : HasFiniteDifferentialSpan (B := B) d g) :
    HasFiniteDifferentialSpan (B := B) d (f * g) := by
  obtain ⟨M, hMfg, hM, hf⟩ := hf
  obtain ⟨N, hNfg, hN, hg⟩ := hg
  exact ⟨M * N, hMfg.mul hNfg, differential_mul_stable d M N hM hN,
    Submodule.mul_mem_mul hf hg⟩

/-- Every iterate remains in an actual differential-stable subspace. -/
theorem stage14_derivation_iterate_mem (d : Derivation k R R)
    (M : Submodule B R) (hM : ∀ x ∈ M, d x ∈ M) {f : R} (hf : f ∈ M)
    (n : ℕ) : ((d : R → R)^[n]) f ∈ M := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    simpa only [Function.iterate_succ_apply'] using hM _ ih

/-- In a finite stable subspace M, the first finrank(M)+1 derivatives have a
nonzero linear relation. Finite dimensionality is derived from M.FG. -/
theorem finiteStableSubspace_nontrivial_relation (d : Derivation k R R)
    (M : Submodule B R) (hMfg : M.FG) (hM : ∀ x ∈ M, d x ∈ M)
    {f : R} (hf : f ∈ M) :
    ∃ c : Fin (Module.finrank B M + 1) → B,
      (∃ i, c i ≠ 0) ∧ ∑ i, c i • ((d : R → R)^[i.val]) f = 0 := by
  letI : FiniteDimensional B M := (Submodule.fg_iff_finiteDimensional M).mp hMfg
  let v : Fin (Module.finrank B M + 1) → M :=
    fun i => ⟨((d : R → R)^[i.val]) f, stage14_derivation_iterate_mem d M hM hf i.val⟩
  have hdep : ¬ LinearIndependent B v := by
    intro h
    have hcard := h.fintype_card_le_finrank
    simp only [Fintype.card_fin] at hcard
    exact (Nat.not_succ_le_self _ hcard)
  obtain ⟨c, hc, hne⟩ := Fintype.not_linearIndependent_iff.mp hdep
  refine ⟨c, hne, ?_⟩
  have heq := congrArg (fun x : M => (x : R)) hc
  simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero] using heq

/-- A finite differential span produces, rather than assumes, the scalar ODE. -/
theorem finiteDifferentialSpan_has_relation (d : Derivation k R R) {f : R}
    (hf : HasFiniteDifferentialSpan (B := B) d f) :
    HasScalarLinearDifferentialRelation (B := B) d f := by
  obtain ⟨M, hMfg, hM, hf⟩ := hf
  exact ⟨Module.finrank B M, finiteStableSubspace_nontrivial_relation d M hMfg hM hf⟩

/-- Concrete scalar differential-equation closure under addition from finite
stable witnesses, with neither the output subspace nor the relation assumed. -/
theorem finiteDifferentialSpan_add_relation (d : Derivation k R R) {f g : R}
    (hf : HasFiniteDifferentialSpan (B := B) d f)
    (hg : HasFiniteDifferentialSpan (B := B) d g) :
    HasScalarLinearDifferentialRelation (B := B) d (f + g) :=
  finiteDifferentialSpan_has_relation d (finiteDifferentialSpan_add d hf hg)

/-- Concrete scalar differential-equation closure under multiplication. -/
theorem finiteDifferentialSpan_mul_relation (d : Derivation k R R) {f g : R}
    (hf : HasFiniteDifferentialSpan (B := B) d f)
    (hg : HasFiniteDifferentialSpan (B := B) d g) :
    HasScalarLinearDifferentialRelation (B := B) d (f * g) :=
  finiteDifferentialSpan_has_relation d (finiteDifferentialSpan_mul d hf hg)

end StrictEUnit
