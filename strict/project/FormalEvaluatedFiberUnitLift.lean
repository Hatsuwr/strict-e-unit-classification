import FormalDomainFiberUnitLift
import AlgebraicFiberDomain

/-! Final formal-candidate assembly at the current checkpoint. An actual
injective evaluation of its whole algebraic fiber into a domain supplies
H-domain. The formal fundamental matrix, its invertibility/ODE, and the
fiber evaluation/injectivity remain explicit mathematical assumptions.
No numerical E-value evaluation or Beukers injectivity is constructed here. -/
noncomputable section
open scoped TensorProduct
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] formalAmbientBaseAlgebra
attribute [local instance] laurentLogPointAlgebra laurentLogPointTower
variable {k L : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  [CommRing L] [IsDomain L] [Algebra k L]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (N : ℕ) (hN : N ≠ 0)
  (Y : Matrix n n (RatFunc (LaurentSeries k))) (A : Matrix n n (LaurentLogBase k))
  (hdet : Y.det ≠ 0)
  (hy : ∀ i j, formalAmbientDerivation N hN (Y i j) =
    ∑ l, formalBaseEmbedding (A i l) * Y l j)
local notation "Cand" => matrixGeneratedAlgebra (B := LaurentLogBase k) Y

/-- A supplied injective whole-fiber evaluation into a domain replaces the
separately supplied H-domain premise. The actual algebraic chart and general
tensor-unit theorem provide the remainder of the regular-unit lift. -/
def formalCandidate_fiber_unit_lift_of_injective_evaluation
    (ν : (k ⊗[LaurentLogBase k] Cand) →ₐ[k] L) (hν : Function.Injective ν) :=
  letI := formalCandidate_faithfullyFlat N hN Y A hdet hy
  formalCandidate_fiber_unit_lift_of_domain N hN Y A hdet hy
    (group_isDomain_of_injective_fiber_evaluation
      (formalCandidateMultiplicationEquiv N hN Y A hdet hy) ν hν)

#check @formalCandidate_fiber_unit_lift_of_injective_evaluation
#print axioms formalCandidate_fiber_unit_lift_of_injective_evaluation
end StrictEUnit
