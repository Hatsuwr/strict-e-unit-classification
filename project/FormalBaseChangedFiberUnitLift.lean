import Stage22FormalCandidateEvaluation
import FormalEvaluatedFiberUnitLift
noncomputable section
open scoped TensorProduct
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
attribute [local instance 2000] formalAmbientBaseAlgebra formalAmbientBaseTower
attribute [local instance] laurentLogPointAlgebra laurentLogPointTower
variable {k K : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  [CommRing K] [IsDomain K] [Algebra k K]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (F : Matrix n n (LaurentSeries k)) (Z : (Matrix n n (LaurentLogBase k))ˣ)
local notation "Y" => Matrix.map F RatFunc.C * Matrix.map (Z : Matrix n n (LaurentLogBase k))
  (algebraMap (LaurentLogBase k) (RatFunc (LaurentSeries k)))
local notation "Cand" => matrixGeneratedAlgebra (B:=LaurentLogBase k) Y
/-- The proved whole-fiber regular-unit lift, specialized to an actual
base-changed formal coefficient matrix before choosing the coefficient field. -/
def formalBaseChangedFiberUnitLift
    (N : ℕ) (hN : N ≠ 0) (A : Matrix n n (LaurentLogBase k))
    (hdet : Matrix.det Y ≠ 0)
    (hy : ∀ i j, formalAmbientDerivation N hN (Y i j) =
      ∑ l, formalBaseEmbedding (A i l) * Y l j)
    (ξ : (k ⊗[LaurentLogBase k] Cand) →ₐ[k] K)
    (hξ : Function.Injective ξ) :=
  formalCandidate_fiber_unit_lift_of_injective_evaluation
    (k:=k) (L:=K) (n:=n) N hN Y A hdet hy ξ hξ
end StrictEUnit
#print axioms StrictEUnit.formalBaseChangedFiberUnitLift
