import GenericNumericalScalarDescent
noncomputable section
open scoped TensorProduct
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
attribute [local instance 2000] formalAmbientBaseAlgebra formalAmbientBaseTower
attribute [local instance] laurentLogPointAlgebra laurentLogPointTower
variable {k L : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  [CommRing L] [IsDomain L] [Algebra k L]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (F : Matrix n n (LaurentSeries k)) (Z : (Matrix n n (LaurentLogBase k))ˣ)
local notation "Y" => Matrix.map F RatFunc.C * Matrix.map (Z : Matrix n n (LaurentLogBase k))
  (algebraMap (LaurentLogBase k) (RatFunc (LaurentSeries k)))
local notation "Cand" => matrixGeneratedAlgebra (B:=LaurentLogBase k) Y

theorem formalCandidate_genericUnitExponentialForm
    (k₀ : Subfield ℂ) (τ : L →+* ℂ)
    (ν : formalMatrixCoefficientAlgebra F →ₐ[k] L)
    (hclass : ∀ s : formalMatrixCoefficientAlgebra F, IsUnit s →
      HasExponentialForm k₀ (τ (ν s))) (v : Candˣ) :
    HasExponentialForm k₀ (τ (formalMatrixCandidateEvaluation F Z ν (v : Cand))) := by
  obtain ⟨s, hs, he, hval⟩ :=
    formalMatrixCandidateEvaluation_unit F Z ν (v : Cand) v.isUnit
  rw [hval]
  exact hclass s hs

/-- Assemble the complete numerical conclusion before specializing either carrier. -/
def formalCandidate_genericExponentialForm
    (k₀ : Subfield ℂ) (τ : L →+* ℂ)
    (hmem : ∀ a : k, τ (algebraMap k L a) ∈ k₀)
    (N : ℕ) (hN : N ≠ 0) (A : Matrix n n (LaurentLogBase k))
    (hdet : Matrix.det Y ≠ 0)
    (hy : ∀ i j, formalAmbientDerivation N hN (Y i j) =
      ∑ l, formalBaseEmbedding (A i l) * Y l j)
    (ν : formalMatrixCoefficientAlgebra F →ₐ[k] L)
    (ξ : (k ⊗[LaurentLogBase k] Cand) →ₐ[k] L)
    (hξ : Function.Injective ξ)
    (hcompat : ∀ r : Cand, ξ ((1:k) ⊗ₜ[LaurentLogBase k] r) =
      formalMatrixCandidateEvaluation F Z ν r)
    (hclass : ∀ s : formalMatrixCoefficientAlgebra F, IsUnit s →
      HasExponentialForm k₀ (τ (ν s))) :=
  formalCandidate_genericNumericalCore F Z k₀ τ hmem ν ξ
    (fun r => hcompat r) (formalCandidate_genericUnitExponentialForm F Z k₀ τ ν hclass)
    (formalBaseChangedScalarUnitLift F Z N hN A hdet hy ξ hξ)
end StrictEUnit
#print axioms StrictEUnit.formalCandidate_genericUnitExponentialForm
#print axioms StrictEUnit.formalCandidate_genericExponentialForm
