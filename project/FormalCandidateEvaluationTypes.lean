import GenericFormalUnitNumericalDescent
noncomputable section
open scoped TensorProduct
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
attribute [local instance 2000] formalAmbientBaseAlgebra formalAmbientBaseTower
attribute [local instance] laurentLogPointAlgebra laurentLogPointTower
variable {k L : Type*} [Field k] [CommRing L] [Algebra k L]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (F : Matrix n n (LaurentSeries k)) (Z : (Matrix n n (LaurentLogBase k))ˣ)
local notation "Y" => Matrix.map F RatFunc.C * Matrix.map (Z : Matrix n n (LaurentLogBase k))
  (algebraMap (LaurentLogBase k) (RatFunc (LaurentSeries k)))
local notation "Cand" => matrixGeneratedAlgebra (B:=LaurentLogBase k) Y
/-- This is exactly the whole-fiber algebra-hom type, with generic instance paths. -/
abbrev formalCandidateFiberEvaluationType := (k ⊗[LaurentLogBase k] Cand) →ₐ[k] L
/-- Exactly the existing pure-tensor specialization compatibility proposition. -/
abbrev formalCandidateFiberCompatibility
    (ν : formalMatrixCoefficientAlgebra F →ₐ[k] L)
    (ξ : formalCandidateFiberEvaluationType (k:=k) (L:=L) F Z) :=
  ∀ r : Cand, ξ ((1:k) ⊗ₜ[LaurentLogBase k] r) = formalMatrixCandidateEvaluation F Z ν r
end StrictEUnit
