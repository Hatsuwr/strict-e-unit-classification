import FormalBaseChangedFiberUnitLift
noncomputable section
open scoped TensorProduct
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
attribute [local instance 2000] formalAmbientBaseAlgebra formalAmbientBaseTower
attribute [local instance] laurentLogPointAlgebra laurentLogPointTower
/-- Projection of already-proved witnesses; no new existence assumption is added. -/
theorem scalarPartOfFourfoldExists {X V B A : Type*}
    {P : X → Prop} {Q : X → V → Prop} {R : V → B → Prop} {S : V → A → Prop}
    (h : ∃ x : X, ∃ v : V, ∃ b : B, ∃ a : A,
      P x ∧ Q x v ∧ R v b ∧ S v a) : ∃ v : V, ∃ a : A, S v a := by
  obtain ⟨x, v, b, a, hp, hq, hr, hs⟩ := h
  exact ⟨v, a, hs⟩

variable {k K : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  [CommRing K] [IsDomain K] [Algebra k K]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (F : Matrix n n (LaurentSeries k)) (Z : (Matrix n n (LaurentLogBase k))ˣ)
local notation "Y" => Matrix.map F RatFunc.C * Matrix.map (Z : Matrix n n (LaurentLogBase k))
  (algebraMap (LaurentLogBase k) (RatFunc (LaurentSeries k)))
local notation "Cand" => matrixGeneratedAlgebra (B:=LaurentLogBase k) Y
/-- The scalar-unit component of the full proved lift, with its exact
proposition inferred from the generic construction rather than reconstructed. -/
def formalBaseChangedScalarUnitLift
    (N : ℕ) (hN : N ≠ 0) (A : Matrix n n (LaurentLogBase k))
    (hdet : Matrix.det Y ≠ 0)
    (hy : ∀ i j, formalAmbientDerivation N hN (Y i j) =
      ∑ l, formalBaseEmbedding (A i l) * Y l j)
    (ξ : (k ⊗[LaurentLogBase k] Cand) →ₐ[k] K)
    (hξ : Function.Injective ξ) :=
  fun u => scalarPartOfFourfoldExists
    (formalBaseChangedFiberUnitLift (k:=k) (K:=K) F Z N hN A hdet hy ξ hξ u)
end StrictEUnit
#check @StrictEUnit.formalBaseChangedScalarUnitLift
#print axioms StrictEUnit.formalBaseChangedScalarUnitLift
