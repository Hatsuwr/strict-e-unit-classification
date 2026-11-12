import ConstructedPVFiberUnitLift

/-! Actual matrix-generated candidate specialization. Faithful flatness,
finite type, tensor-chart bijectivity and candidate constants are proved inputs,
not additional hypotheses. Tensor-unit factorization remains explicit. -/
noncomputable section
open scoped TensorProduct
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
variable {k B L n : Type*} [Field k] [IsAlgClosed k] [CommRing B] [IsDomain B]
  [UniqueFactorizationMonoid B] [IsNoetherianRing B] [Field L]
  [Algebra k B] [Algebra k L] [Algebra B L] [IsScalarTower k B L]
  [Algebra B k] [IsScalarTower k B k] [Fintype n] [DecidableEq n]
variable (dB : Derivation k B B) (dL : Derivation k L L)
  (Y : Matrix n n L) (A : Matrix n n B) (hdet : Y.det ≠ 0)
  (hb : ∀ b, dL (algebraMap B L b) = algebraMap B L (dB b))
  (hy : ∀ i j, dL (Y i j) = ∑ l, algebraMap B L (A i l) * Y l j)
  (hsimple : ∀ I : Ideal B, (∀ x ∈ I, dB x ∈ I) → I ≠ ⊥ → I = ⊤)
  (hc : ∀ a, dL a = 0 → ∃ c:k, algebraMap k L c = a)
/-- Transparent proof-valued specialization, retaining the complete inferred
factorization hypothesis and conclusion of the generic theorem. -/
def candidate_fiber_unit_lift :=
  letI := matrixGeneratedAlgebra_faithfullyFlat dB dL Y A hdet hb hy hsimple
  constructedPV_fiber_unit_lift dB
    (candidateKDerivation dB dL Y A hb hy)
    (candidateKDerivation_base dB dL Y A hb hy)
    (faithfullyFlatCandidateMultiplication_bijective dB dL Y A hdet hb hy hsimple hc)
    (candidateKDerivation_constants dB dL Y A hb hy hc)

#check @candidate_fiber_unit_lift
#print axioms candidate_fiber_unit_lift
end StrictEUnit
