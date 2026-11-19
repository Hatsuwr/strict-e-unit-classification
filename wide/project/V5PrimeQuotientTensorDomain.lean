import AlgebraicTensorDomain
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.FiniteStability

noncomputable section
open scoped TensorProduct
namespace StrictEUnit
variable {k C H : Type*} [Field k] [IsAlgClosed k]
  [CommRing C] [CommRing H] [Algebra k C] [Algebra k H]

/-- Tensoring an arbitrary domain with a finite-type prime quotient over an
algebraically closed field gives a domain. C need not be of finite type. -/
theorem v5_primeQuotient_tensor_isDomain [IsDomain C] [Algebra.FiniteType k H]
    (I : Ideal H) [I.IsPrime] : IsDomain (C ⊗[k] (H ⧸ I)) :=
  algebraic_tensor_isDomain (k := k) (A := C) (B := H ⧸ I)

/-- The same assertion in the opposite tensor order. -/
theorem v5_primeQuotient_tensor_left_isDomain [IsDomain C] [Algebra.FiniteType k H]
    (I : Ideal H) [I.IsPrime] : IsDomain ((H ⧸ I) ⊗[k] C) := by
  letI := v5_primeQuotient_tensor_isDomain (k := k) (C := C) I
  exact (Algebra.TensorProduct.comm k (H ⧸ I) C).toMulEquiv.isDomain

/-- The square of a prime finite-type quotient is a domain. No assertion
about a Hopf quotient structure or identity component is included. -/
theorem v5_primeQuotient_tensorSquare_isDomain [Algebra.FiniteType k H]
    (I : Ideal H) [I.IsPrime] : IsDomain ((H ⧸ I) ⊗[k] (H ⧸ I)) :=
  v5_primeQuotient_tensor_isDomain (k := k) (C := H ⧸ I) I

/-- The left-associated tensor cube is also a domain. -/
theorem v5_primeQuotient_tensorCube_isDomain [Algebra.FiniteType k H]
    (I : Ideal H) [I.IsPrime] : IsDomain (((H ⧸ I) ⊗[k] (H ⧸ I)) ⊗[k] (H ⧸ I)) := by
  letI := v5_primeQuotient_tensorSquare_isDomain (k := k) I
  exact v5_primeQuotient_tensor_isDomain (k := k) (C := (H ⧸ I) ⊗[k] (H ⧸ I)) I

/-- Mixed tensor C⊗(H/I)⊗(H/I), useful for coassociativity of a restricted
coaction. The coalgebra/coaction laws are not assumed or constructed here. -/
theorem v5_primeQuotient_mixedTriple_isDomain [IsDomain C] [Algebra.FiniteType k H]
    (I : Ideal H) [I.IsPrime] : IsDomain ((C ⊗[k] (H ⧸ I)) ⊗[k] (H ⧸ I)) := by
  letI := v5_primeQuotient_tensor_isDomain (k := k) (C := C) I
  exact v5_primeQuotient_tensor_isDomain (k := k) (C := C ⊗[k] (H ⧸ I)) I

end StrictEUnit
#print axioms StrictEUnit.v5_primeQuotient_tensor_isDomain
#print axioms StrictEUnit.v5_primeQuotient_tensor_left_isDomain
#print axioms StrictEUnit.v5_primeQuotient_tensorSquare_isDomain
#print axioms StrictEUnit.v5_primeQuotient_tensorCube_isDomain
#print axioms StrictEUnit.v5_primeQuotient_mixedTriple_isDomain
