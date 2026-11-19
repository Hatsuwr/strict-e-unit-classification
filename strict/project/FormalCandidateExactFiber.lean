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
/-- The existing exact-kernel fiber construction specialized to the canonical
formal candidate, before choosing an actual arithmetic matrix. -/
def formalCandidateExactFiber
    (hk : RingHom.ker (e).toRingHom =
  Ideal.map (algebraMap (LaurentLogBase k) C)
    (RingHom.ker (algebraMap (LaurentLogBase k) k))) : (k ⊗[LaurentLogBase k] C) →ₐ[k] K :=
  exactKernelFiberEvaluation (k:=k) (B:=LaurentLogBase k) (R:=C) e hk

theorem formalCandidateExactFiber_injective
    (hk : RingHom.ker (e).toRingHom =
  Ideal.map (algebraMap (LaurentLogBase k) C)
    (RingHom.ker (algebraMap (LaurentLogBase k) k))) :
    Function.Injective (formalCandidateExactFiber F Z ν hk) :=
  by
  unfold formalCandidateExactFiber
  apply exactKernelFiberEvaluation_injective

@[simp] theorem formalCandidateExactFiber_specialization
    (hk : RingHom.ker (e).toRingHom =
  Ideal.map (algebraMap (LaurentLogBase k) C)
    (RingHom.ker (algebraMap (LaurentLogBase k) k))) (r : C) :
    formalCandidateExactFiber F Z ν hk
      (algebraicFiberSpecialization (k:=k) (B:=LaurentLogBase k) r) = e r :=
  by
  unfold formalCandidateExactFiber
  apply exactKernelFiberEvaluation_specialization
end StrictEUnit

#print StrictEUnit.formalCandidateExactFiber
#print axioms StrictEUnit.formalCandidateExactFiber
