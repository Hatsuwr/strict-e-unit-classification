import Stage22FiberUnitNumericalDescent
import Stage25AbstractNumericalDescent
import GenericFormalInverseValuesDescent

/-! Generic numerical descent combines injective inverse-value lifting with
the proved regular-unit argument before any concrete arithmetic realization
is substituted. All application hypotheses remain explicit. -/
noncomputable section
open scoped TensorProduct
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] formalAmbientBaseAlgebra
attribute [local instance 2000] formalAmbientBaseTower
attribute [local instance] laurentLogPointAlgebra laurentLogPointTower
attribute [local instance 2000] Algebra.toModule
attribute [local instance 2000] stage22CanonicalScalarCommRing stage22CanonicalScalarCommSemiring
attribute [local instance 2000] stage22CanonicalScalarSemiring stage22CanonicalScalarAddCommMonoid
attribute [local instance 2000] stage22CanonicalScalarMonoid stage22CanonicalComplexCommRing
attribute [local instance 2000] stage22CanonicalComplexSemiring stage22CanonicalCandidateCommRing
attribute [local instance 2000] stage22CanonicalCandidateSemiring stage22CanonicalCandidateAddCommMonoid
attribute [local instance 2000] stage22CanonicalCandidateMonoid
variable (k : Subfield ℂ) [IsAlgClosed k]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (F : Matrix n n (LaurentSeries k)) (Z : (Matrix n n (LaurentLogBase k))ˣ)
local notation "Y" => (Matrix.map F RatFunc.C) * (Matrix.map (Z : Matrix n n (LaurentLogBase k))
  (algebraMap (LaurentLogBase k) (RatFunc (LaurentSeries k))))
local notation "Cand" => matrixGeneratedAlgebra (B := LaurentLogBase k) Y

/-- Reciprocal values in one injective whole-fiber image have exponential
form after the genuine coefficient-unit classification is supplied. -/
theorem stage25_inverseValues_exponential_form
    (N : ℕ) (hN : N ≠ 0) (A : Matrix n n (LaurentLogBase k))
    (hdet : Matrix.det Y ≠ 0)
    (hy : ∀ i j, formalAmbientDerivation N hN (Y i j) =
      ∑ l, formalBaseEmbedding (A i l) * Y l j)
    (ν : formalMatrixCoefficientAlgebra F →ₐ[k] ℂ)
    (ξ : formalCandidateFiberEvaluationType (k:=k) (L:=ℂ) F Z)
    (hξ : Function.Injective ξ)
    (hcompat : formalCandidateFiberCompatibility F Z ν ξ)
    (hclass : ∀ s : formalMatrixCoefficientAlgebra F, IsUnit s →
      HasExponentialForm k (ν s))
    (u : ℂ) (hu : u ≠ 0) (ha : u ∈ ξ.range) (hb : u⁻¹ ∈ ξ.range) :
    HasExponentialForm k u := by
  exact formalCandidate_genericInverseValuesExponentialForm (k:=k) (L:=ℂ) F Z k
    (RingHom.id ℂ) (fun _ _ h => h) (fun a => a.property)
    N hN A hdet hy ν ξ hξ hcompat hclass u hu ha hb

end StrictEUnit
#print axioms StrictEUnit.stage25_inverseValues_exponential_form
