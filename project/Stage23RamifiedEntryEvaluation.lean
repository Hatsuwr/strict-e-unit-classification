import Stage19RamifiedFrameUnits
import Stage23GenericCandidateRestriction
import Stage23EntryAlgebraPresentation

/-! Restrict the already constructed genuine candidate evaluation to the actual
ramified entry algebra and prove its generator values. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
attribute [local instance 2000] formalAmbientBaseAlgebra
attribute [local instance 2000] formalAmbientBaseTower
variable (k : Subfield ℂ) (N : ℕ) (hN : N ≠ 0)
    {n : Type*} [Fintype n] [DecidableEq n]
    (F : Matrix n n (subfieldEntireFunctionAlgebra k))
    (hstrict : ∀ i j, IsStrictEFunction (F i j).val.val)
    (hd : ∀ z : ℂ, z ≠ 0 → (F.map (stage14_subfieldEntireEvaluation k z)).det ≠ 0)
    (Z : (Matrix n n (LaurentLogBase k))ˣ)
local notation "G" => stage19_formalMatrix k N (stage19_ramifiedBoundedMatrix k N hN F hstrict)
local notation "Y" => stage17_formalFrame k N hN F
local notation "EntryRing" => matrixEntryAlgebra (B:=LaurentLogBase k) Y
local notation "Candidate" => matrixGeneratedAlgebra (B:=LaurentLogBase k)
  ((Matrix.map G RatFunc.C) * Matrix.map (Z : Matrix n n (LaurentLogBase k))
    (algebraMap (LaurentLogBase k) (RatFunc (LaurentSeries k))))

/-- The actual pre-localization algebra lies in the unchanged candidate after
any invertible base change. -/
theorem stage23_ramifiedEntry_le_candidate : EntryRing ≤ Candidate := by
  let hframe := stage19_ramifiedFormalMatrix_compatibility k N hN F hstrict
  let hchange := matrixGeneratedAlgebra_mul_base_unit (B:=LaurentLogBase k) (Matrix.map G RatFunc.C) Z
  exact (matrixEntryAlgebra_le (B:=LaurentLogBase k) Y).trans
    (le_of_eq ((congrArg (matrixGeneratedAlgebra (B:=LaurentLogBase k)) hframe.symm).trans
      hchange.symm))

include hstrict hd Z

/-- Restrict the Stage22 whole-candidate evaluation, using the actual Stage19
coefficient evaluation, to the actual Stage17 frame-entry algebra. -/
def stage23_ramifiedEntryEvaluation : EntryRing →ₐ[k] ℂ :=
  stage23_genericCandidateRestriction (k:=k) (K:=ℂ) G Z
    (stage19_ramifiedGeneratedEvaluation k N hN F hstrict hd) EntryRing
    (stage23_ramifiedEntry_le_candidate k N hN F hstrict Z)

/-- Each formal matrix entry evaluates to the original entire entry at one. -/
theorem stage23_ramifiedEntryEvaluation_entry (ij : n × n) :
    stage23_ramifiedEntryEvaluation k N hN F hstrict hd Z
      (stage23_entry (k:=k) Y ij) = (F ij.1 ij.2).val.val 1 := by
  have h := stage23_genericCandidateRestriction_coefficient (k:=k) (K:=ℂ) G Z
    (stage19_ramifiedGeneratedEvaluation k N hN F hstrict hd) EntryRing
    (stage23_ramifiedEntry_le_candidate k N hN F hstrict Z)
    (stage23_entry (k:=k) Y ij)
    (stage19_generatedEntry k N (stage19_ramifiedBoundedMatrix k N hN F hstrict) ij.1 ij.2)
    (congrFun (congrFun (stage19_ramifiedFormalMatrix_compatibility k N hN F hstrict)
      ij.1) ij.2).symm
  exact h.trans (stage19_ramifiedGeneratedEvaluation_entry k N hN F hstrict hd ij.1 ij.2)

/-- The t-coordinate value is one, derived from its genuine analytic source. -/
theorem stage23_ramifiedEntryEvaluation_coordinate :
    stage23_ramifiedEntryEvaluation k N hN F hstrict hd Z
      (manuscriptParameterUnit (k:=k) (R:=EntryRing) : EntryRing) = 1 := by
  have h := stage23_genericCandidateRestriction_coefficient (k:=k) (K:=ℂ) G Z
    (stage19_ramifiedGeneratedEvaluation k N hN F hstrict hd) EntryRing
    (stage23_ramifiedEntry_le_candidate k N hN F hstrict Z)
    (manuscriptParameterUnit (k:=k) (R:=EntryRing) : EntryRing)
    (stage19_generatedLaurentPolynomial k N
      (stage19_ramifiedBoundedMatrix k N hN F hstrict) (LaurentPolynomial.T 1))
    (formalBaseEmbedding_C (LaurentPolynomial.T 1))
  exact h.trans (stage19_generatedEvaluation_coordinate k N
    (stage19_ramifiedBoundedMatrix k N hN F hstrict)
    (stage19_ramifiedBoundedMatrix_det_nonzero k N hN F hstrict hd) ⟨1, one_ne_zero⟩)

/-- The logarithm value is zero under the same existing numerical map. -/
theorem stage23_ramifiedEntryEvaluation_log :
    stage23_ramifiedEntryEvaluation k N hN F hstrict hd Z
      (manuscriptLogParameter (k:=k) (R:=EntryRing)) = 0 := by
  exact stage23_genericCandidateRestriction_log (k:=k) (K:=ℂ) G Z
    (stage19_ramifiedGeneratedEvaluation k N hN F hstrict hd) EntryRing
    (stage23_ramifiedEntry_le_candidate k N hN F hstrict Z)
    (manuscriptLogParameter (k:=k) (R:=EntryRing)) formalBaseEmbedding_X

end StrictEUnit
