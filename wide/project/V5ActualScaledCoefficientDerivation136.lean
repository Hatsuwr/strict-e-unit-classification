import V5ActualScaledSolutionFactor136
noncomputable section
open scoped TensorProduct
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1800
set_option synthInstance.maxHeartbeats 15000
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing
namespace StrictEUnit
/-- Additive operators on a tensor product agree when they agree on pure tensors. -/
theorem v5TensorAddHom_ext136 {B U V Z : Type*} [CommRing B] [CommRing U] [CommRing V]
    [Algebra B U] [Algebra B V] [AddCommMonoid Z]
    (D E : U ⊗[B] V →+ Z) (h : ∀ u v, D (u ⊗ₜ[B] v) = E (u ⊗ₜ[B] v)) :
    ∀ x, D x = E x := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul u v => exact h u v
  | add x y hx hy => rw [map_add, map_add, hx, hy]
attribute [local instance 6000] solutionRing136 solutionAddGroup136 solutionAddMonoid136
  solutionCoefficientAlgebra136 solutionLaurentAlgebra136 solutionLaurentModule136
  solutionTensorCoefficientAlgebra136 reversedSolutionCoefficientAlgebra136
variable {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → entireFunctionAlgebra) (A : Matrix ι ι V5LaurentBase)
    (hA : ∀ z : ℂˣ, ∀ i, deriv (f i).val (z : ℂ) =
      ∑ j, arithmeticLaurentEvaluation z (A i j) * (f j).val (z : ℂ))
    [Algebra V5LaurentBase V5LaurentBase]
    (q : ℕ)
    (hpower : ∀ p, algebraMap V5LaurentBase V5LaurentBase p = v5LaurentPower q p)
/-- The common-scaled coefficient tensor rule identifies its operator with
the actual reversed solution-Kummer derivation. The rule is the constructor's
pure-tensor formula, rather than a differential hypothesis. -/
theorem v5ActualScaledCoefficientDerivation136
    (D : V5LaurentBase ⊗[V5LaurentBase] v5WideSolutionAlgebra f →+
      V5LaurentBase ⊗[V5LaurentBase] v5WideSolutionAlgebra f)
    (hD : ∀ l s, D (l ⊗ₜ[V5LaurentBase] s) =
      v5LaurentEulerDerivation127 l ⊗ₜ[V5LaurentBase] s +
        l ⊗ₜ[V5LaurentBase] v5CoordinateEuler136
          ((q : V5LaurentBase) * LaurentPolynomial.T 1) (v5WideSolutionDerivation f A hA) s) :
    ∀ x, D x = v5ActualReversedSolutionKummerDifferential136 f A hA q hpower x := by
  apply v5TensorAddHom_ext136 D
    (v5ActualReversedSolutionKummerDifferential136 f A hA q hpower).toAddMonoidHom
  intro l s
  change D (l ⊗ₜ[V5LaurentBase] s) =
    v5ActualReversedSolutionKummerDifferential136 f A hA q hpower (l ⊗ₜ[V5LaurentBase] s)
  rw [hD, v5ActualReversedSolutionKummerDifferential136_tmul,
    v5ActualScaledSolutionFactor136]
  rw [v5LaurentEulerDerivation127_apply]
/-- The same comparison with exactly the product-form rule of the scaled
Kummer coefficient constructor. -/
theorem v5ActualScaledCoefficientDerivation_mul136
    (D : V5LaurentBase ⊗[V5LaurentBase] v5WideSolutionAlgebra f →+
      V5LaurentBase ⊗[V5LaurentBase] v5WideSolutionAlgebra f)
    (hD : ∀ l s, D (l ⊗ₜ[V5LaurentBase] s) =
      v5LaurentEulerDerivation127 l ⊗ₜ[V5LaurentBase] s +
        l ⊗ₜ[V5LaurentBase] (algebraMap V5LaurentBase (v5WideSolutionAlgebra f)
          ((q : V5LaurentBase) * LaurentPolynomial.T 1) * v5WideSolutionDerivation f A hA s)) :
    ∀ x, D x = v5ActualReversedSolutionKummerDifferential136 f A hA q hpower x :=
  v5ActualScaledCoefficientDerivation136 f A hA q hpower D hD
end StrictEUnit
#print axioms StrictEUnit.v5TensorAddHom_ext136
#print axioms StrictEUnit.v5ActualScaledCoefficientDerivation136
#print axioms StrictEUnit.v5ActualScaledCoefficientDerivation_mul136
