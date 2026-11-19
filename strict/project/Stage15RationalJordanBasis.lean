import RationalRamificationWeights
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Algebra.DirectSum.Module

/-! A rational generalized eigenbasis constructed from the actual endomorphism.
The spanning hypothesis is proved below for algebraically closed coefficient
fields with rational eigenvalues. No diagonalization or Jordan form is assumed. -/
noncomputable section
namespace StrictEUnit
open Module
variable {k n : Type*} [Field k] [CharZero k] [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- A genuine basis assembled from the rational generalized eigenspaces. The
second conclusion records the block support of its coordinate functions. -/
theorem stage15_rational_generalized_eigenbasis
    (f : Module.End k (n → k))
    (hspan : (⨆ q : ℚ, f.genEigenspace (q : k) (Module.finrank k (n → k))) = ⊤) :
    ∃ (b : Basis n k (n → k)) (q : n → ℚ),
      (∀ i, b i ∈ f.genEigenspace (q i : k) (Module.finrank k (n → k))) ∧
      (∀ (a : ℚ) (x : n → k), x ∈ f.genEigenspace (a : k) (Module.finrank k (n → k)) →
        ∀ i, q i ≠ a → b.repr x i = 0) := by
  classical
  let E : ℚ → Submodule k (n → k) := fun a =>
    f.genEigenspace (a : k) (Module.finrank k (n → k))
  have hi : iSupIndep E :=
    (f.independent_genEigenspace (Module.finrank k (n → k))).comp Rat.cast_injective
  have hd : DirectSum.IsInternal E :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hi hspan
  let v := fun a : ℚ => Module.finBasis k (E a)
  let b₀ := hd.collectedBasis v
  let e := b₀.indexEquiv (Pi.basisFun k n)
  refine ⟨b₀.reindex e, fun i => (e.symm i).1, ?_, ?_⟩
  · intro i
    simpa only [Basis.reindex_apply] using hd.collectedBasis_mem v (e.symm i)
  · intro a x hx i hi
    change b₀.repr x (e.symm i) = 0
    exact hd.collectedBasis_repr_of_mem_ne v (Ne.symm hi) hx

omit [CharZero k] [DecidableEq n] in
/-- Over an algebraically closed field, rationality of every eigenvalue gives
spanning by rational generalized eigenspaces at a uniform dimension bound. -/
theorem stage15_rational_generalized_eigenspaces_span [IsAlgClosed k]
    (f : Module.End k (n → k))
    (hrat : ∀ a : k, f.HasEigenvalue a → ∃ q : ℚ, (q : k) = a) :
    (⨆ q : ℚ, f.genEigenspace (q : k) (Module.finrank k (n → k))) = ⊤ := by
  apply top_unique
  rw [← f.iSup_maxGenEigenspace_eq_top]
  refine iSup_le fun a => ?_
  by_cases ha : f.maxGenEigenspace a = ⊥
  · rw [ha]; exact bot_le
  · obtain ⟨q, rfl⟩ := hrat a (Module.End.HasUnifEigenvalue.lt zero_lt_one ha)
    exact (f.genEigenspace_le_genEigenspace_finrank (q : k) ⊤).trans (le_iSup (fun r : ℚ => f.genEigenspace (r : k) (Module.finrank k (n → k))) q)

end StrictEUnit
