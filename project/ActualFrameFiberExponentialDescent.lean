import GenericCoefficientUnitClassification
import GenericExactFiberNumericalDescent
import FormalCandidateExactFiberCompatibility
import Stage24CommonFrameValueCoverage
import Stage23ActualFrameFiber
import Stage25InverseValuesDescent
import AlgebraicScalarExponential

/-! Conditional end-to-end classification from two explicitly unproved inputs:
common arithmetic-frame availability and exact Beukers relation lifting.
Neither input is declared as an axiom, and neither is proved by this file.
All intermediate formal/analytic/fiber/unit interfaces are derived. -/
noncomputable section
open scoped TensorProduct
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] formalAmbientBaseAlgebra
attribute [local instance 2000] formalAmbientBaseTower
attribute [local instance 10] laurentLogPointAlgebra laurentLogPointTower
attribute [local instance 2000] Algebra.toModule
attribute [local instance 2000] stage22CanonicalScalarCommRing stage22CanonicalScalarCommSemiring
attribute [local instance 2000] stage22CanonicalScalarSemiring stage22CanonicalScalarAddCommMonoid
attribute [local instance 2000] stage22CanonicalScalarMonoid stage22CanonicalComplexCommRing
attribute [local instance 2000] stage22CanonicalComplexSemiring stage22CanonicalCandidateCommRing
attribute [local instance 2000] stage22CanonicalCandidateSemiring stage22CanonicalCandidateAddCommMonoid
attribute [local instance 2000] stage22CanonicalCandidateMonoid
attribute [local instance 2000] stage19CoefficientMonoid
local notation "k₀" => IntermediateField.toSubfield (algebraicClosure ℚ ℂ)

variable {n : Type} [Fintype n] [DecidableEq n]
  (hBeukers : StrictELaurentRelationLifting)
  (N : ℕ) (hN : N ≠ 0)
  (B : Matrix n n (LaurentPolynomial k₀)) (M : Matrix n n k₀)
  (F : Matrix n n (subfieldEntireFunctionAlgebra k₀))
  (hstrict : ∀ i j, IsStrictEFunction (F i j).val.val)
  (hF : Stage17ActualEulerFrameRelation k₀ B M F)
  (h1 : (F.map (stage14_subfieldEntireEvaluation k₀ 1)).det ≠ 0)
  (Z : (Matrix n n (LaurentLogBase k₀))ˣ)
local notation "G" => stage19_formalMatrix k₀ N (stage19_ramifiedBoundedMatrix k₀ N hN F hstrict)
local notation "Y" => Matrix.map G RatFunc.C * Matrix.map (Z : Matrix n n (LaurentLogBase k₀))
  (algebraMap (LaurentLogBase k₀) (RatFunc (LaurentSeries k₀)))
local notation "hd" => stage23_arithmeticFrame_det_nonzero_off_origin k₀ B M F hF h1
local notation "ν" => stage19_ramifiedGeneratedEvaluation k₀ N hN F hstrict hd

/-- The actual ramified coefficient algebra uses its proved arithmetic unit classification. -/
theorem actualRamifiedCoefficientExponentialForm
    (s : formalMatrixCoefficientAlgebra G) (hs : IsUnit s) : HasExponentialForm k₀ (ν s) := by
  obtain ⟨c, a, hc, he⟩ := stage19_ramifiedGenerated_unit_value k₀ N hN F hstrict hd s hs
  exact ⟨c, c.property, by exact_mod_cast hc, a, a.property, he⟩

include hBeukers M hF h1

/-- Actual frame values descend through the entire exact numerical fiber. -/
def actualFrameFiber_inverseValuesPreCore
    (hdet : Matrix.det Y ≠ 0)
    (hy : ∀ i j, formalAmbientDerivation N hN (Y i j) =
      ∑ l, formalBaseEmbedding ((B.map (stage17_laurentBasePullback k₀ N)) i l) * Y l j)
 :=
  letI : IsAlgClosed k₀ := stage17_algebraicTaylorField_isAlgClosed
  formalCandidate_exactInverseValuesExponentialForm (k:=k₀) (K:=ℂ) G Z ν k₀
    (RingHom.id ℂ) (fun _ _ h => h) (fun a => a.property) N hN
    (B.map (stage17_laurentBasePullback k₀ N)) hdet hy
    (stage23_actualCandidate_exact_kernel hBeukers N hN B M F hstrict hF h1 Z)



/-- The same actual coefficient classification in the generic inherited monoid structure. -/
def actualFrameCoefficientClassification :=
  coefficientUnitClassification_from_semiringMonoid G k₀ (RingHom.id ℂ) ν
    (actualRamifiedCoefficientExponentialForm N hN B M F hstrict hF h1)

/-- Apply the genuine coefficient-unit theorem to the exact-fiber descent. -/
def actualFrameFiber_inverseValuesCore
    (hdet : Matrix.det Y ≠ 0)
    (hy : ∀ i j, formalAmbientDerivation N hN (Y i j) =
      ∑ l, formalBaseEmbedding ((B.map (stage17_laurentBasePullback k₀ N)) i l) * Y l j) :=
  actualFrameFiber_inverseValuesPreCore hBeukers N hN B M F hstrict hF h1 Z hdet hy
    (actualFrameCoefficientClassification N hN B M F hstrict hF h1)

/-- Actual frame values descend through the entire exact numerical fiber. -/
theorem actualFrameFiber_inverseValuesExponentialForm
    (hdet : Matrix.det Y ≠ 0)
    (hy : ∀ i j, formalAmbientDerivation N hN (Y i j) =
      ∑ l, formalBaseEmbedding ((B.map (stage17_laurentBasePullback k₀ N)) i l) * Y l j)
    (u : ℂ) (hu : u ≠ 0)
    (ha : u ∈ Algebra.adjoin k₀ (Set.range fun ij : n × n => (F ij.1 ij.2).val.val 1))
    (hb : u⁻¹ ∈ Algebra.adjoin k₀ (Set.range fun ij : n × n => (F ij.1 ij.2).val.val 1)) :
    HasExponentialForm k₀ u := by
  have hrange := stage23_actualFiberEvaluation_frameValues_le_range
    hBeukers N hN B M F hstrict hF h1 Z
  unfold stage23_actualFiberEvaluation at hrange
  exact actualFrameFiber_inverseValuesCore hBeukers N hN B M F hstrict hF h1 Z hdet hy
    u hu (hrange ha) (hrange hb)

end StrictEUnit
#print axioms StrictEUnit.actualRamifiedCoefficientExponentialForm
#print axioms StrictEUnit.actualFrameFiber_inverseValuesExponentialForm

#print axioms StrictEUnit.actualFrameFiber_inverseValuesCore

#print axioms StrictEUnit.actualFrameFiber_inverseValuesPreCore
#print axioms StrictEUnit.actualFrameCoefficientClassification
