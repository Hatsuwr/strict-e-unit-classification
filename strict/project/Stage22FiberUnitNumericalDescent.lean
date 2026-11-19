import FormalCandidateEvaluationTypes
import GenericFormalUnitNumericalDescent
import GenericNumericalScalarDescent
import CanonicalStructureProjections
import NumericalScalarUnitDescent
import FormalBaseChangedScalarUnitLift
import Stage22FormalCandidateEvaluation
import FormalEvaluatedFiberUnitLift
import ArithmeticRecovery

/-! Final numerical descent through the actual regular-unit lift. The entire
fiber evaluation, its injectivity and compatibility, and the coefficient-unit
classification remain explicit inputs. No strict-E classification is asserted
without those application premises. -/
noncomputable section
open scoped TensorProduct
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
attribute [local instance 2000] formalAmbientBaseAlgebra
attribute [local instance 2000] formalAmbientBaseTower
attribute [local instance] laurentLogPointAlgebra laurentLogPointTower
local instance stage22CanonicalScalarCommRing (k : Subfield ℂ) : CommRing k :=
  canonicalFieldCommRing k
local instance stage22CanonicalScalarCommSemiring (k : Subfield ℂ) : CommSemiring k :=
  canonicalFieldCommSemiring k
local instance stage22CanonicalScalarSemiring (k : Subfield ℂ) : Semiring k :=
  canonicalFieldSemiring k
local instance stage22CanonicalScalarAddCommMonoid (k : Subfield ℂ) : AddCommMonoid k :=
  canonicalFieldAddCommMonoid k
local instance stage22CanonicalScalarMonoid (k : Subfield ℂ) : Monoid k :=
  canonicalFieldMonoid k
local instance stage22CanonicalComplexCommRing : CommRing ℂ := inferInstance
local instance stage22CanonicalComplexSemiring : Semiring ℂ := canonicalRingSemiring ℂ

variable (k : Subfield ℂ) [IsAlgClosed k]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (F : Matrix n n (LaurentSeries k)) (Z : (Matrix n n (LaurentLogBase k))ˣ)
local notation "Y" => (Matrix.map F RatFunc.C) * (Matrix.map (Z : Matrix n n (LaurentLogBase k))
  (algebraMap (LaurentLogBase k) (RatFunc (LaurentSeries k))))
local notation "Cand" => matrixGeneratedAlgebra (B := LaurentLogBase k) Y

local instance stage22CanonicalCandidateCommRing : CommRing Cand := (Cand).toCommRing
local instance stage22CanonicalCandidateSemiring : Semiring Cand := canonicalRingSemiring Cand
local instance stage22CanonicalCandidateAddCommMonoid : AddCommMonoid Cand :=
  canonicalRingAddCommMonoid Cand
local instance stage22CanonicalCandidateMonoid : Monoid Cand := canonicalRingMonoid Cand

/-- A whole-fiber numerical unit has the claimed form once the actual formal
system, exact fiber embedding and coefficient-ring unit classification are
supplied. The regular unit lift and scalar comparison are proved dependencies. -/
def formalCandidate_fiberUnit_exponential_form
    (N : ℕ) (hN : N ≠ 0) (A : Matrix n n (LaurentLogBase k))
    (hdet : Matrix.det Y ≠ 0)
    (hy : ∀ i j, formalAmbientDerivation N hN (Y i j) =
      ∑ l, formalBaseEmbedding (A i l) * Y l j)
    (ν : formalMatrixCoefficientAlgebra F →ₐ[k] ℂ)
    (ξ : formalCandidateFiberEvaluationType (k:=k) (L:=ℂ) F Z)
    (hξ : Function.Injective ξ)
    (hcompat : formalCandidateFiberCompatibility F Z ν ξ)
    (hclass : ∀ s : formalMatrixCoefficientAlgebra F, IsUnit s →
      HasExponentialForm k (ν s))
    := formalCandidate_genericExponentialForm (k:=k) (L:=ℂ) F Z k
      (RingHom.id ℂ) (fun a => a.property) N hN A hdet hy ν ξ hξ hcompat hclass

end StrictEUnit
#print axioms StrictEUnit.formalCandidate_fiberUnit_exponential_form

#check @StrictEUnit.formalCandidate_fiberUnit_exponential_form
