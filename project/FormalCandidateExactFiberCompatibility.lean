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
variable {k K : Type*} [Field k] [CommRing K] [Algebra k K]
    {n : Type*} [Fintype n] [DecidableEq n]
    (F : Matrix n n (LaurentSeries k)) (Z : (Matrix n n (LaurentLogBase k))ˣ)
    (ν : formalMatrixCoefficientAlgebra F →ₐ[k] K)
local notation "C" => matrixGeneratedAlgebra (B:=LaurentLogBase k)
  (Matrix.map F RatFunc.C * Matrix.map (Z : Matrix n n (LaurentLogBase k))
    (algebraMap (LaurentLogBase k) (RatFunc (LaurentSeries k))))
local notation "e" => formalMatrixCandidateEvaluation F Z ν
/-- The exact-fiber constructor satisfies the original compatibility proposition. -/
theorem formalCandidateExactFiber_compatibility
    (hk : RingHom.ker (e).toRingHom =
      Ideal.map (algebraMap (LaurentLogBase k) C)
        (RingHom.ker (algebraMap (LaurentLogBase k) k))) :
    formalCandidateFiberCompatibility F Z ν (formalCandidateExactFiber F Z ν hk) := by
  intro r
  exact formalCandidateExactFiber_specialization F Z ν hk r
end StrictEUnit
#print axioms StrictEUnit.formalCandidateExactFiber_compatibility
