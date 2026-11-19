import V5WideOwnTensorEmbedding
import Mathlib.RingTheory.Localization.BaseChange

noncomputable section
open scoped TensorProduct
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 30000
namespace StrictEUnit

section Generic
variable (B E : Type*) [CommRing B] [IsDomain B] [Field E] [Algebra B E]
  [FaithfulSMul B E]

/-- The localized scalar structure extending the original faithful action. -/
local instance : Algebra (FractionRing B) E := FractionRing.liftAlgebra B E
local instance : IsScalarTower B (FractionRing B) E := FractionRing.isScalarTower_liftAlgebra B E

def v5FractionScalarTensorEquiv :
    E ⊗[FractionRing B] E ≃ₐ[FractionRing B] E ⊗[B] E :=
  IsLocalization.algebraTensorEquiv (nonZeroDivisors B) (FractionRing B) E E

/-- Reducedness over the fraction field implies reducedness over the domain. -/
theorem v5_reducedTensor_of_fraction_reduced
    (h : IsReduced (E ⊗[FractionRing B] E)) :
    IsReduced (E ⊗[B] E) := by
  letI := h
  exact isReduced_of_injective (v5FractionScalarTensorEquiv B E).symm.toAlgHom
    (v5FractionScalarTensorEquiv B E).symm.injective
end Generic

attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
variable {k : Type*} [Field k] [CharZero k] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial k))

omit [CharZero k] in
theorem v5WidePointedBaseToLaurent_injective :
    Function.Injective (algebraMap (LaurentPolynomial k) (LaurentSeries k)) := by
  change Function.Injective (v5WidePointedLaurentBase k)
  exact HahnSeries.ofPowerSeries_injective.comp (v5WidePointedBase_injective (K := k))

local instance v5WideFaithfulScalarAction :
    FaithfulSMul (LaurentPolynomial k) (LaurentSeries k) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr v5WidePointedBaseToLaurent_injective

local instance : Algebra (FractionRing (LaurentPolynomial k)) (LaurentSeries k) :=
  FractionRing.liftAlgebra (LaurentPolynomial k) (LaurentSeries k)

/-- Full concrete reduction to a tensor square of characteristic-zero fields over
a field. The fraction-tensor reducedness hypothesis remains explicit. -/
def v5WideOwnConstants_reduced_of_fractionTensor
    (h : IsReduced (LaurentSeries k ⊗[FractionRing (LaurentPolynomial k)] LaurentSeries k)) :=
  letI := v5_reducedTensor_of_fraction_reduced (LaurentPolynomial k) (LaurentSeries k) h
  v5WideOwnConstants_reduced_of_fieldTensor A
end StrictEUnit
#print axioms StrictEUnit.v5FractionScalarTensorEquiv
#print axioms StrictEUnit.v5_reducedTensor_of_fraction_reduced
#print axioms StrictEUnit.v5WidePointedBaseToLaurent_injective
#print axioms StrictEUnit.v5WideOwnConstants_reduced_of_fractionTensor
