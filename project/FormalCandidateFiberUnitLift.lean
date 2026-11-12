import ManuscriptCandidateFiberUnitLift
import FormalCandidateCoaction
import LaurentLogBasePoint

/-! Actual formal ambient field and actual algebraic basepoint t=1, ell=0.
No faithful-flatness, finite-type, constants, or torsor hypotheses are supplied.
The fundamental matrix/ODE and tensor-unit factorization remain inputs.
The algebraic fiber is not identified with numerical E-function values. -/
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
variable (N:ℕ) (hN:N≠0)
  (Y : Matrix n n (RatFunc (LaurentSeries k))) (A : Matrix n n (LaurentLogBase k))
  (hdet : Y.det ≠ 0)
  (hy : ∀ i j, formalAmbientDerivation N hN (Y i j) =
    ∑ l, formalBaseEmbedding (A i l) * Y l j)
omit [CharZero k] [IsAlgClosed k] in
/-- The selected base action is the actual formal embedding, not evaluation
through the algebraic basepoint. -/
theorem formalFiber_base_map (b : LaurentLogBase k) :
    algebraMap (LaurentLogBase k) (RatFunc (LaurentSeries k)) b =
      formalBaseEmbedding b := rfl

omit [IsAlgClosed k] in
/-- Compatibility expressed in the precise algebraMap form of the candidate API. -/
theorem formalFiber_base_compatible (b : LaurentLogBase k) :
    formalAmbientDerivation N hN (algebraMap (LaurentLogBase k) (RatFunc (LaurentSeries k)) b) =
      algebraMap (LaurentLogBase k) (RatFunc (LaurentSeries k))
        (manuscriptBaseDerivation (k := k) N b) := by
  change formalAmbientDerivation N hN (formalBaseEmbedding b) =
    formalBaseEmbedding (manuscriptBaseDerivation (k := k) N b)
  exact formalBaseEmbedding_differential N hN b

/-- Proof-valued specialization with its exact inferred proposition printed
below: a fiber unit is a scalar unit times the specialization of an actual
regular candidate unit satisfying a first-order base-coefficient equation. -/
def formalCandidate_fiber_unit_lift :=
  manuscriptCandidate_fiber_unit_lift N hN (formalAmbientDerivation N hN) Y A hdet
    (formalFiber_base_compatible N hN) hy
    (fun x hx => (formalAmbientDerivation_constants N hN x).mp hx)

#check @formalCandidate_fiber_unit_lift
#print axioms formalFiber_base_map
#print axioms formalFiber_base_compatible
#print axioms formalCandidate_fiber_unit_lift
end StrictEUnit
