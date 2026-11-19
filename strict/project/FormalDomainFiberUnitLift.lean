import FormalCandidateFiberUnitLift
import DomainUnitCharacters

/-! The strongest formal candidate fiber-unit lift with the tensor-unit
factorization input discharged. Domain of its actual diagonal constants
algebra is still an explicit hypothesis. The actual formal solution matrix
and its ODE are supplied, and the algebraic fiber is not identified with
numerical E-function values. -/
noncomputable section
open scoped TensorProduct
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] formalAmbientBaseAlgebra
attribute [local instance] laurentLogPointAlgebra laurentLogPointTower
variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (N : ℕ) (hN : N ≠ 0)
  (Y : Matrix n n (RatFunc (LaurentSeries k))) (A : Matrix n n (LaurentLogBase k))
  (hdet : Y.det ≠ 0)
  (hy : ∀ i j, formalAmbientDerivation N hN (Y i j) =
    ∑ l, formalBaseEmbedding (A i l) * Y l j)
local notation "baseD" => manuscriptBaseDerivation (k := k) N
local notation "candD" => candidateKDerivation baseD (formalAmbientDerivation N hN) Y A
  (formalFiber_base_compatible N hN) hy
local notation "candBase" => candidateKDerivation_base baseD (formalAmbientDerivation N hN) Y A
  (formalFiber_base_compatible N hN) hy
local notation "H" => pvConstantAlgebra
  (R := matrixGeneratedAlgebra (B := LaurentLogBase k) Y) baseD candD candBase

/-- An actual algebraic-fiber unit lifts, up to a scalar unit, to a regular
candidate unit satisfying a first-order base-coefficient equation. The former
factorization assumption is proved, while domain of the actual H is visible
as the remaining structural input. The exact inferred proposition is checked below. -/
def formalCandidate_fiber_unit_lift_of_domain (hDomain : IsDomain H) :=
  letI := hDomain
  formalCandidate_fiber_unit_lift N hN Y A hdet hy (fun w => tensor_unit_is_pure w)

#check @formalCandidate_fiber_unit_lift_of_domain
#print axioms formalCandidate_fiber_unit_lift_of_domain
end StrictEUnit
