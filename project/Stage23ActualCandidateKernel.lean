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
/-- The actual base-changed candidate is the same inverse-adjoined entry ring. -/
theorem stage23_actualCandidate_eq_adjoin_inverse :
    Candidate = Algebra.adjoin (LaurentLogBase k₀)
      (insert (Matrix.det Y)⁻¹ (EntryRing : Set (RatFunc (LaurentSeries k₀)))) := by
  exact (matrixGeneratedAlgebra_mul_base_unit (B:=LaurentLogBase k₀)
    (Matrix.map G RatFunc.C) Z).trans
      ((congrArg (matrixGeneratedAlgebra (B:=LaurentLogBase k₀))
        (stage19_ramifiedFormalMatrix_compatibility k₀ N hN F hstrict)).trans
        (matrixGeneratedAlgebra_eq_adjoin_inverse Y))

include hBeukers B M hF h1

/-- The actual entry evaluation has precisely the proved lifted relation kernel. -/
theorem stage23_actualCandidate_entry_kernel :
    RingHom.ker (stage23_ramifiedEntryEvaluation k₀ N hN F hstrict hd Z).toRingHom =
      Ideal.map (algebraMap (LaurentLogBase k₀) EntryRing)
        (RingHom.ker (algebraMap (LaurentLogBase k₀) k₀)) := by
  exact stage23_actual_entry_exact_kernel hBeukers N hN B M F hstrict hF
    (stage23_ramifiedEntryEvaluation k₀ N hN F hstrict hd Z)
    (stage23_ramifiedEntryEvaluation_entry k₀ N hN F hstrict hd Z)
    (stage23_ramifiedEntryEvaluation_coordinate k₀ N hN F hstrict hd Z)
    (stage23_ramifiedEntryEvaluation_log k₀ N hN F hstrict hd Z)

/-- The full candidate's exact kernel is derived from the actual analytic
polynomial lifts and the proved actual determinant localization. -/
theorem stage23_actualCandidate_exact_kernel :
    RingHom.ker (Eval).toRingHom =
      Ideal.map (algebraMap (LaurentLogBase k₀) Candidate)
        (RingHom.ker (algebraMap (LaurentLogBase k₀) k₀)) := by
  have hR := stage23_actualCandidate_entry_kernel hBeukers N hN B M F hstrict hF h1 Z
  have hdet : Matrix.det Y ≠ 0 := stage17_formalFrame_det_ne_zero k₀ N hN F (hd 1 one_ne_zero)
  have hS := stage23_actualCandidate_eq_adjoin_inverse N hN F hstrict Z
  exact stage23_subalgebra_localized_kernel (k:=k₀) (K:=ℂ) EntryRing Candidate
    (stage23_ramifiedEntry_le_candidate k₀ N hN F hstrict Z) (matrixEntryDet Y)
    (fun h => hdet (congrArg Subtype.val h)) hS Eval hR


end StrictEUnit
