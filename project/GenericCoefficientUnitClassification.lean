import GenericExactFiberNumericalDescent
import Stage19GeneratedUnitClassification
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
/-- Compare two inherited monoid projections before specializing the formal matrix. -/
theorem coefficientUnitClassification_from_semiringMonoid
    {k K : Type*} [Field k] [CommRing K] [Algebra k K]
    {n : Type*} [Fintype n] [DecidableEq n]
    (F : Matrix n n (LaurentSeries k)) (k₀ : Subfield ℂ) (τ : K →+* ℂ)
    (ν : formalMatrixCoefficientAlgebra F →ₐ[k] K)
    (hclass : ∀ s : formalMatrixCoefficientAlgebra F,
      @IsUnit _ (stage19CoefficientMonoid F) s → HasExponentialForm k₀ (τ (ν s))) :
    ∀ s : formalMatrixCoefficientAlgebra F, IsUnit s → HasExponentialForm k₀ (τ (ν s)) := by
  intro s hs
  exact hclass s hs
end StrictEUnit
#print axioms StrictEUnit.coefficientUnitClassification_from_semiringMonoid
