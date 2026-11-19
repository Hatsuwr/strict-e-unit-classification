import V5LaurentPointOne
open scoped TensorProduct
noncomputable section
namespace StrictEUnit
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
attribute [-instance] Polynomial.commSemiring HahnSeries.instModule HahnSeries.instSMul
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k S : Type*} [Field k] [CommRing S]
  [Algebra k S] [Algebra (LaurentPolynomial k) S]
  [IsScalarTower k (LaurentPolynomial k) S]
local instance : Algebra (LaurentPolynomial k) k :=
  (v5LaurentPointOne (k := k)).toRingHom.toAlgebra
local instance : IsScalarTower k (LaurentPolynomial k) k :=
  IsScalarTower.of_algebraMap_eq' (v5LaurentPointOne (k := k)).comp_algebraMap.symm

def v5LaurentPointOneQuotientAlg :
    (S ⧸ Ideal.span {algebraMap (LaurentPolynomial k) S (LaurentPolynomial.T 1) - 1}) ≃ₐ[k]
      k ⊗[LaurentPolynomial k] S := by
  refine AlgEquiv.ofRingEquiv (f := v5LaurentPointOneQuotient (k := k) (S := S)) ?_
  intro c
  change v5LaurentPointOneQuotient (k := k) (S := S)
    (Ideal.Quotient.mk _ (algebraMap k S c)) = _
  rw [v5LaurentPointOneQuotient_mk]
  rw [Algebra.algebraMap_eq_smul_one]
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  simp only [smul_eq_mul, mul_one]
  rfl

@[simp] theorem v5LaurentPointOneQuotientAlg_mk (s : S) :
    v5LaurentPointOneQuotientAlg (k := k) (S := S) (Ideal.Quotient.mk _ s) =
      (1 : k) ⊗ₜ[LaurentPolynomial k] s :=
  v5LaurentPointOneQuotient_mk s

def v5LaurentQuotientAtIdealAlg (I : Ideal S)
    (hi : I = Ideal.span {algebraMap (LaurentPolynomial k) S (LaurentPolynomial.T 1) - 1}) :=
  (Ideal.quotientEquivAlgOfEq k hi).trans (v5LaurentPointOneQuotientAlg (k := k) (S := S))

@[simp] theorem v5LaurentQuotientAtIdealAlg_mk (I : Ideal S)
    (hi : I = Ideal.span {algebraMap (LaurentPolynomial k) S (LaurentPolynomial.T 1) - 1}) (s : S) :
    v5LaurentQuotientAtIdealAlg (k := k) I hi (Ideal.Quotient.mk _ s) =
      (1 : k) ⊗ₜ[LaurentPolynomial k] s := by
  simp [v5LaurentQuotientAtIdealAlg]
end StrictEUnit
#print axioms StrictEUnit.v5LaurentPointOneQuotientAlg

#print axioms StrictEUnit.v5LaurentQuotientAtIdealAlg
#print axioms StrictEUnit.v5LaurentQuotientAtIdealAlg_mk
