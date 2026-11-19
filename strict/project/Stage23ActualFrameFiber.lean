import FormalCandidateExactFiber
import Stage23ActualCandidateKernel
import Stage23EntryKernel
import Stage23RamifiedEntryEvaluation
import Stage23LocalizedCandidateKernel
import Stage23ExactFiberEvaluation
import Stage17ConstructedFormalFundamental
import Stage23ArithmeticFrameNonvanishing

/-! The actual arithmetic frame, conditional on the explicitly named Beukers
polynomial-lifting input, yields an injective k-algebra evaluation of the entire
intended numerical tensor fiber. It is compatible with the existing Stage22
candidate evaluation and its Stage19 genuine analytic coefficient realization. -/
noncomputable section
open scoped TensorProduct
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
attribute [local instance 2000] formalAmbientBaseAlgebra
attribute [local instance 2000] formalAmbientBaseTower
attribute [local instance 10] laurentLogPointAlgebra laurentLogPointTower
local notation "k₀" => IntermediateField.toSubfield (algebraicClosure ℚ ℂ)
variable (hBeukers : StrictELaurentRelationLifting)
    {n : Type} [Fintype n] [DecidableEq n]
    (N : ℕ) (hN : N ≠ 0)
    (B : Matrix n n (LaurentPolynomial k₀)) (M : Matrix n n k₀)
    (F : Matrix n n (subfieldEntireFunctionAlgebra k₀))
    (hstrict : ∀ i j, IsStrictEFunction (F i j).val.val)
    (hF : Stage17ActualEulerFrameRelation k₀ B M F)
    (h1 : (F.map (stage14_subfieldEntireEvaluation k₀ 1)).det ≠ 0)
    (Z : (Matrix n n (LaurentLogBase k₀))ˣ)
local notation "G" => stage19_formalMatrix k₀ N (stage19_ramifiedBoundedMatrix k₀ N hN F hstrict)
local notation "Y" => stage17_formalFrame k₀ N hN F
local notation "EntryRing" => matrixEntryAlgebra (B:=LaurentLogBase k₀) Y
local notation "Candidate" => matrixGeneratedAlgebra (B:=LaurentLogBase k₀)
  ((Matrix.map G RatFunc.C) * Matrix.map (Z : Matrix n n (LaurentLogBase k₀))
    (algebraMap (LaurentLogBase k₀) (RatFunc (LaurentSeries k₀))))
local notation "hd" => stage23_arithmeticFrame_det_nonzero_off_origin k₀ B M F hF h1
local notation "ν" => stage19_ramifiedGeneratedEvaluation k₀ N hN F hstrict hd
local notation "Eval" => formalMatrixCandidateEvaluation (k:=k₀) (K:=ℂ) G Z ν
include hBeukers B M hF h1

/-- The actual numerical evaluation of the whole tensor fiber at (t,ell)=(1,0).
Its existence and k-linearity are constructed, not supplied as hypotheses. -/
@[irreducible] def stage23_actualFiberEvaluation :=
  formalCandidateExactFiber (k:=k₀) (K:=ℂ) (n:=n) G Z ν
    (stage23_actualCandidate_exact_kernel hBeukers N hN B M F hstrict hF h1 Z)

/-- The entire intended fiber embeds, not merely the reduced numerical image. -/
theorem stage23_actualFiberEvaluation_injective :
    Function.Injective (stage23_actualFiberEvaluation hBeukers N hN B M F hstrict hF h1 Z) :=
  by
  unfold stage23_actualFiberEvaluation
  apply formalCandidateExactFiber_injective

/-- The constructed fiber map is exactly compatible with the pre-existing
whole-candidate evaluation used by the regular-unit descent theorem. -/
@[simp] theorem stage23_actualFiberEvaluation_specialization (r : Candidate) :
    stage23_actualFiberEvaluation hBeukers N hN B M F hstrict hF h1 Z
      (algebraicFiberSpecialization (k:=k₀) (B:=LaurentLogBase k₀) r) = Eval r :=
  by
  unfold stage23_actualFiberEvaluation
  exact formalCandidateExactFiber_specialization (k:=k₀) (K:=ℂ) G Z ν
    (stage23_actualCandidate_exact_kernel hBeukers N hN B M F hstrict hF h1 Z) r

/-- Literal finite frame-value algebra membership implies membership in the
range of the injective whole-fiber evaluation. -/
theorem stage23_actualFiberEvaluation_frameValues_le_range :
    Algebra.adjoin k₀ (Set.range fun ij : n × n => (F ij.1 ij.2).val.val 1) ≤
      (stage23_actualFiberEvaluation hBeukers N hN B M F hstrict hF h1 Z).range := by
  apply Algebra.adjoin_le
  rintro x ⟨ij, rfl⟩
  let r : Candidate :=
    (Subalgebra.inclusion (stage23_ramifiedEntry_le_candidate k₀ N hN F hstrict Z))
      (stage23_entry (k:=k₀) Y ij)
  apply (AlgHom.mem_range (stage23_actualFiberEvaluation hBeukers N hN B M F hstrict hF h1 Z)).2
  refine ⟨algebraicFiberSpecialization (k:=k₀) (B:=LaurentLogBase k₀) r, ?_⟩
  refine (stage23_actualFiberEvaluation_specialization hBeukers N hN B M F hstrict hF h1 Z r).trans ?_
  exact (formalMatrixCandidateEvaluation_coefficient (k:=k₀) (K:=ℂ) G Z ν r
    (stage19_generatedEntry k₀ N (stage19_ramifiedBoundedMatrix k₀ N hN F hstrict) ij.1 ij.2)
    (congrFun (congrFun (stage19_ramifiedFormalMatrix_compatibility k₀ N hN F hstrict)
      ij.1) ij.2).symm).trans
      (stage19_ramifiedGeneratedEvaluation_entry k₀ N hN F hstrict hd ij.1 ij.2)

end StrictEUnit
