import V5WideTensorFractionBridge
import V5CharZeroFieldTensorReduced

noncomputable section
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 30000
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing
namespace StrictEUnit

variable {k : Type*} [Field k] [CharZero k] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial k))

local instance : FaithfulSMul (LaurentPolynomial k) (LaurentSeries k) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr v5WidePointedBaseToLaurent_injective

local instance : Algebra (FractionRing (LaurentPolynomial k)) (LaurentSeries k) :=
  FractionRing.liftAlgebra (LaurentPolynomial k) (LaurentSeries k)

/-- Reducedness of the actual own-PV coordinate algebra, with no extra reducedness
assumption. The concrete tensor embedding and generic reduced field-tensor
theorem together eliminate the earlier conditional premise. -/
def v5WideOwnConstants_isReduced :=
  have h₁ : Function.Injective (algebraMap k (LaurentPolynomial k)) := by
    intro x y h
    apply (algebraMap k (LaurentSeries k)).injective
    simpa only [(v5WidePointedLaurentBase k).commutes] using
      congrArg (v5WidePointedLaurentBase k) h
  letI : CharZero (LaurentPolynomial k) := charZero_of_injective_algebraMap h₁
  letI : CharZero (FractionRing (LaurentPolynomial k)) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective (LaurentPolynomial k)
      (FractionRing (LaurentPolynomial k)))
  v5WideOwnConstants_reduced_of_fractionTensor A
    (v5_charZero_field_tensor_reduced (FractionRing (LaurentPolynomial k))
      (LaurentSeries k) (LaurentSeries k))
end StrictEUnit
#print axioms StrictEUnit.v5WideOwnConstants_isReduced
#check StrictEUnit.v5WideOwnConstants_isReduced
