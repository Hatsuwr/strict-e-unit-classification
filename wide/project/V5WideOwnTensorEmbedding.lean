import V5WideOwnPVAction
import Mathlib.RingTheory.Flat.Domain
import Mathlib.RingTheory.Nilpotent.Defs

noncomputable section
open scoped TensorProduct
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule
attribute [-instance] HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
namespace StrictEUnit

/-- Embedding both flat source factors into any B-algebra preserves
injectivity over the domain B; no flatness of the target is assumed. -/
theorem v5_flatDomainTensorMap_injective
    {B R E : Type*} [CommRing B] [IsDomain B] [CommRing R] [CommRing E]
    [Algebra B R] [Algebra B E] [Module.Flat B R]
    (f : R →ₐ[B] E) (hf : Function.Injective f) :
    Function.Injective (Algebra.TensorProduct.map f f) :=
  TensorProduct.map_injective_of_flat_flat_of_isDomain f.toLinearMap f.toLinearMap hf hf

variable {k : Type*} [Field k] [CharZero k] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial k))

/-- Faithful flatness needed for the embedding is a proved property of the
actual centered matrix candidate, not a new premise. -/
theorem v5WideOwnCandidate_faithfullyFlat :
    Module.FaithfullyFlat (LaurentPolynomial k) (V5WideFieldCandidate A) :=
  matrixGeneratedAlgebra_faithfullyFlat v5LaurentBaseDerivation
    stage14_laurentAlgebraDerivation (v5WidePointedLaurentFundamental A) A
    (v5WideOwnFundamental_det_ne_zero A) v5WideOwnBase_differential
    (v5WideOwnFundamental_ode A) v5LaurentBase_stable_ideal_eq_top

/-- The actual own-PV constants embed in the ambient Laurent-field tensor
square over the original Laurent-polynomial base. -/
def v5WideOwnConstantsToFieldTensor :
    V5WideOwnConstants A →ₐ[k]
      LaurentSeries k ⊗[LaurentPolynomial k] LaurentSeries k :=
  ((Algebra.TensorProduct.map (V5WideFieldCandidate A).val
    (V5WideFieldCandidate A).val).restrictScalars k).comp
      (pvConstantAlgebra v5LaurentBaseDerivation (v5WideOwnDerivation A)
        (v5WideOwnDerivation_base A)).val

theorem v5WideOwnConstantsToFieldTensor_injective :
    Function.Injective (v5WideOwnConstantsToFieldTensor A) := by
  letI := v5WideOwnCandidate_faithfullyFlat A
  exact (v5_flatDomainTensorMap_injective (V5WideFieldCandidate A).val
    Subtype.val_injective).comp Subtype.val_injective

/-- Explicit reduction target, not an unconditional reducedness theorem.
The remaining input is reducedness of the ambient field tensor square. -/
theorem v5WideOwnConstants_reduced_of_fieldTensor
    [IsReduced (LaurentSeries k ⊗[LaurentPolynomial k] LaurentSeries k)] :
    IsReduced (V5WideOwnConstants A) :=
  isReduced_of_injective (v5WideOwnConstantsToFieldTensor A)
    (v5WideOwnConstantsToFieldTensor_injective A)

end StrictEUnit
#print axioms StrictEUnit.v5_flatDomainTensorMap_injective
#print axioms StrictEUnit.v5WideOwnCandidate_faithfullyFlat
#print axioms StrictEUnit.v5WideOwnConstantsToFieldTensor_injective
#print axioms StrictEUnit.v5WideOwnConstants_reduced_of_fieldTensor
