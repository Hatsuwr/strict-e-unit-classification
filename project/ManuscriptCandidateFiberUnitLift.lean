import CandidateFiberUnitLift
import LaurentLogBasePoint

/-! Specialization to the actual manuscript base and its t=1, ell=0 point. -/
noncomputable section
open scoped TensorProduct
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance] laurentLogPointAlgebra laurentLogPointTower
variable {k L n : Type*} [Field k] [CharZero k] [IsAlgClosed k] [Field L]
  [Algebra k L] [Algebra (LaurentLogBase k) L] [IsScalarTower k (LaurentLogBase k) L]
  [Fintype n] [DecidableEq n]
variable (N:ℕ) (hN:N≠0) (dL:Derivation k L L)
  (Y:Matrix n n L) (A:Matrix n n (LaurentLogBase k)) (hdet:Y.det≠0)
  (hb:∀ b, dL (algebraMap (LaurentLogBase k) L b)=
    algebraMap (LaurentLogBase k) L (manuscriptBaseDerivation (k:=k) N b))
  (hy:∀ i j,dL (Y i j)=∑l,algebraMap (LaurentLogBase k) L (A i l)*Y l j)
  (hc:∀ x,dL x=0→∃ c : k,algebraMap k L c=x)
def manuscriptCandidate_fiber_unit_lift :=
  letI := laurentLogBase_uniqueFactorizationMonoid k
  letI := laurentLogBase_isNoetherianRing k
  candidate_fiber_unit_lift (manuscriptBaseDerivation (k:=k) N) dL Y A hdet hb hy
    (manuscriptBase_stable_ideal_eq_top N hN) hc
#check @manuscriptCandidate_fiber_unit_lift
#print axioms manuscriptCandidate_fiber_unit_lift
end StrictEUnit
