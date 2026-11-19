import V5WideSolutionRelativeBase
import V5WideSolutionDifferential
import CandidateFaithfullyFlat

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
open scoped BigOperators
namespace StrictEUnit

variable {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → entireFunctionAlgebra)
    (A : Matrix ι ι V5LaurentBase)
    (hA : ∀ z : ℂˣ, ∀ i, deriv (f i).val (z : ℂ) =
      ∑ j, arithmeticLaurentEvaluation z (A i j) * (f j).val (z : ℂ))

/-- The actual solution coordinates have derivatives in their base-linear span. -/
theorem v5WideSolutionGenerators_stable :
    ∀ x ∈ Set.range (v5WideSolutionEntry f),
      v5WideSolutionDerivation f A hA x ∈
        Submodule.span V5LaurentBase (insert 1 (Set.range (v5WideSolutionEntry f))) := by
  rintro _ ⟨i, rfl⟩
  rw [v5WideSolutionDerivation_entry]
  apply Submodule.sum_mem
  intro j _
  change (A i j) • v5WideSolutionEntry f j ∈ _
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_range_self j)))

/-- Every finite collection in the actual solution algebra lies in a finitely
 generated differential-stable B-module containing 1. -/
theorem v5WideSolution_finite_differential_pieces
    (dB : Derivation AlgebraicComplex V5LaurentBase V5LaurentBase)
    (hb : ∀ b, v5WideSolutionDerivation f A hA (v5WideSolutionBase f b) =
      v5WideSolutionBase f (dB b))
    (t : Finset (v5WideSolutionAlgebra f)) :
    ∃ P : Submodule V5LaurentBase (v5WideSolutionAlgebra f),
      P.FG ∧ (1 : v5WideSolutionAlgebra f) ∈ P ∧
      (∀ x ∈ P, v5WideSolutionDerivation f A hA x ∈ P) ∧ ∀ x ∈ t, x ∈ P := by
  classical
  let s := Set.range (v5WideSolutionEntry f)
  obtain ⟨m, hm⟩ := finite_mem_some_differentialPiece (B := V5LaurentBase) s
    (insert 1 (t : Set (v5WideSolutionAlgebra f))) (t.finite_toSet.insert 1)
    (by rw [show Algebra.adjoin V5LaurentBase s = ⊤ from v5WideSolutionLaurent_generates f]
        exact Set.subset_univ _)
  refine ⟨differentialPiece s m, differentialPiece_fg s (Set.finite_range _) m,
    hm (Set.mem_insert _ _), ?_, ?_⟩
  · exact differentialPiece_stable dB (v5WideSolutionDerivation f A hA) hb s
      (v5WideSolutionGenerators_stable f A hA) m
  · intro x hx
    exact hm (Set.mem_insert_of_mem _ hx)

/-- Faithful flatness of the actual solution algebra, conditional only on
compatibility with the supplied base derivation and differential simplicity
of the Laurent base. No flatness or finite-piece hypothesis is assumed. -/
theorem v5WideSolution_faithfullyFlat
    (dB : Derivation AlgebraicComplex V5LaurentBase V5LaurentBase)
    (hb : ∀ b, v5WideSolutionDerivation f A hA (v5WideSolutionBase f b) =
      v5WideSolutionBase f (dB b))
    (hsimple : ∀ I : Ideal V5LaurentBase, (∀ x ∈ I, dB x ∈ I) → I ≠ ⊥ → I = ⊤) :
    Module.FaithfullyFlat V5LaurentBase (v5WideSolutionAlgebra f) := by
  apply faithfullyFlat_of_finite_differential_pieces dB (v5WideSolutionDerivation f A hA)
    hb hsimple
  exact v5WideSolution_finite_differential_pieces f A hA dB hb

end StrictEUnit
#print axioms StrictEUnit.v5WideSolutionGenerators_stable
#print axioms StrictEUnit.v5WideSolution_finite_differential_pieces
#print axioms StrictEUnit.v5WideSolution_faithfullyFlat
