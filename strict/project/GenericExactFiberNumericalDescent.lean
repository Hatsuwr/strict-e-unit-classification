import GenericFormalInverseValuesDescent
import FormalCandidateExactFiberCompatibility
import FormalCandidateExactFiber
import FormalCandidateEvaluationTypes
import Stage22FormalCandidateEvaluation
import Stage23ExactFiberEvaluation
import LaurentLogBasePointKernel
noncomputable section
open scoped TensorProduct
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
attribute [local instance 2000] formalAmbientBaseAlgebra formalAmbientBaseTower
attribute [local instance 10] laurentLogPointAlgebra laurentLogPointTower
variable {k K : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    [CommRing K] [IsDomain K] [Algebra k K]
    {n : Type*} [Fintype n] [DecidableEq n]
    (F : Matrix n n (LaurentSeries k)) (Z : (Matrix n n (LaurentLogBase k))ˣ)
    (ν : formalMatrixCoefficientAlgebra F →ₐ[k] K)
local notation "C" => matrixGeneratedAlgebra (B:=LaurentLogBase k)
  (Matrix.map F RatFunc.C * Matrix.map (Z : Matrix n n (LaurentLogBase k))
    (algebraMap (LaurentLogBase k) (RatFunc (LaurentSeries k))))
local notation "e" => formalMatrixCandidateEvaluation F Z ν
/-- Construct the exact fiber and discharge injectivity and compatibility before numerical specialization. -/
def formalCandidate_exactInverseValuesExponentialForm
    (k₀ : Subfield ℂ) (τ : K →+* ℂ) (hτ : Function.Injective τ)
    (hmem : ∀ a : k, τ (algebraMap k K a) ∈ k₀)
    (N : ℕ) (hN : N ≠ 0) (A : Matrix n n (LaurentLogBase k))
    (hdet : Matrix.det (Matrix.map F RatFunc.C * Matrix.map (Z : Matrix n n (LaurentLogBase k))
      (algebraMap (LaurentLogBase k) (RatFunc (LaurentSeries k)))) ≠ 0)
    (hy : ∀ i j, formalAmbientDerivation N hN
      ((Matrix.map F RatFunc.C * Matrix.map (Z : Matrix n n (LaurentLogBase k))
        (algebraMap (LaurentLogBase k) (RatFunc (LaurentSeries k)))) i j) =
      ∑ l, formalBaseEmbedding (A i l) *
        ((Matrix.map F RatFunc.C * Matrix.map (Z : Matrix n n (LaurentLogBase k))
          (algebraMap (LaurentLogBase k) (RatFunc (LaurentSeries k)))) l j))
    (hk : RingHom.ker (e).toRingHom =
      Ideal.map (algebraMap (LaurentLogBase k) C)
        (RingHom.ker (algebraMap (LaurentLogBase k) k)))
    (hclass : ∀ s : formalMatrixCoefficientAlgebra F, IsUnit s →
      HasExponentialForm k₀ (τ (ν s))) :=
  formalCandidate_genericInverseValuesExponentialForm F Z k₀ τ hτ hmem N hN A hdet hy ν
    (formalCandidateExactFiber F Z ν hk)
    (formalCandidateExactFiber_injective F Z ν hk)
    (formalCandidateExactFiber_compatibility F Z ν hk) hclass
end StrictEUnit
#print axioms StrictEUnit.formalCandidate_exactInverseValuesExponentialForm
