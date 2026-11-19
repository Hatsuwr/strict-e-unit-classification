import GenericFormalUnitNumericalDescent
import FormalCandidateEvaluationTypes
import Stage22NumericalUnitPreimage
noncomputable section
open scoped TensorProduct
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
attribute [local instance 2000] formalAmbientBaseAlgebra formalAmbientBaseTower
attribute [local instance] laurentLogPointAlgebra laurentLogPointTower

/-- Reciprocal numerical images of an injective ring map come from one unit. -/
theorem numericalInverseValues_of_ringUnitClassification
    (k₀ : Subfield ℂ) {R : Type*} [CommRing R]
    (φ : R →+* ℂ) (hφ : Function.Injective φ)
    (hclass : ∀ v : Rˣ, HasExponentialForm k₀ (φ (v : R)))
    (u : ℂ) (hu : u ≠ 0) (ha : ∃ a : R, φ a = u) (hb : ∃ b : R, φ b = u⁻¹) :
    HasExponentialForm k₀ u := by
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, hb⟩ := hb
  obtain ⟨v, hv, he⟩ := unit_preimage_of_injective_evaluation φ hφ a b
    (by rw [ha, hb]; exact mul_inv_cancel₀ hu)
  rw [← he.trans ha]
  exact hclass v

/-- Convert algebra evaluation to a numerical ring map while its source is abstract. -/
theorem numericalInverseValues_of_algUnitClassification
    {k R L : Type*} [Field k] [CommRing R] [CommRing L]
    [Algebra k R] [Algebra k L]
    (k₀ : Subfield ℂ) (τ : L →+* ℂ) (hτ : Function.Injective τ)
    (ξ : R →ₐ[k] L) (hξ : Function.Injective ξ)
    (hclass : ∀ v : Rˣ, HasExponentialForm k₀ (τ (ξ (v : R))))
    (u : ℂ) (hu : u ≠ 0) (ha : ∃ a : R, τ (ξ a) = u)
    (hb : ∃ b : R, τ (ξ b) = u⁻¹) : HasExponentialForm k₀ u := by
  exact numericalInverseValues_of_ringUnitClassification k₀ (τ.comp ξ.toRingHom)
    (hτ.comp hξ) hclass u hu ha hb

variable {k L : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  [CommRing L] [IsDomain L] [Algebra k L]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (F : Matrix n n (LaurentSeries k)) (Z : (Matrix n n (LaurentLogBase k))ˣ)
local notation "Y" => Matrix.map F RatFunc.C * Matrix.map (Z : Matrix n n (LaurentLogBase k))
  (algebraMap (LaurentLogBase k) (RatFunc (LaurentSeries k)))
local notation "Cand" => matrixGeneratedAlgebra (B:=LaurentLogBase k) Y

/-- Perform reciprocal-image descent before the scalar carrier is specialized. -/
def formalCandidate_genericInverseValuesExponentialForm
    (k₀ : Subfield ℂ) (τ : L →+* ℂ) (hτ : Function.Injective τ)
    (hmem : ∀ a : k, τ (algebraMap k L a) ∈ k₀)
    (N : ℕ) (hN : N ≠ 0) (A : Matrix n n (LaurentLogBase k))
    (hdet : Matrix.det Y ≠ 0)
    (hy : ∀ i j, formalAmbientDerivation N hN (Y i j) =
      ∑ l, formalBaseEmbedding (A i l) * Y l j)
    (ν : formalMatrixCoefficientAlgebra F →ₐ[k] L)
    (ξ : formalCandidateFiberEvaluationType (k:=k) (L:=L) F Z)
    (hξ : Function.Injective ξ)
    (hcompat : formalCandidateFiberCompatibility F Z ν ξ)
    (hclass : ∀ s : formalMatrixCoefficientAlgebra F, IsUnit s →
      HasExponentialForm k₀ (τ (ν s))) :=
  numericalInverseValues_of_algUnitClassification (k:=k) (R:=k ⊗[LaurentLogBase k] Cand)
    (L:=L) k₀ τ hτ ξ hξ
    (formalCandidate_genericExponentialForm F Z k₀ τ hmem N hN A hdet hy ν ξ hξ hcompat hclass)
end StrictEUnit
#print axioms StrictEUnit.numericalInverseValues_of_ringUnitClassification
#print axioms StrictEUnit.formalCandidate_genericInverseValuesExponentialForm

#print axioms StrictEUnit.numericalInverseValues_of_algUnitClassification
