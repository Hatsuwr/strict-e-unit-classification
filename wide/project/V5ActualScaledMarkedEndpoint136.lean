import V5ActualMarkedReverseEndpoint136
import V5TensorMarkedOperatorEndpoint136
import V5ActualScaledCoefficientDerivation136
noncomputable section
open scoped TensorProduct
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1800
set_option synthInstance.maxHeartbeats 20000
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
attribute [local instance 5000] Subalgebra.algebra Subalgebra.algebra' Subalgebra.toCommRing
namespace StrictEUnit
attribute [local instance 6000] solutionRing136 solutionAddGroup136 solutionAddMonoid136
  solutionCoefficientAlgebra136 solutionLaurentAlgebra136 solutionLaurentModule136
  solutionTensorCoefficientAlgebra136 reversedSolutionCoefficientAlgebra136
attribute [local instance 7000] markedRightTensorModule136 markedLeftTensorModule136
variable {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → entireFunctionAlgebra)
    (hf : ∀ i, V5IsBroadEFunction (f i).val)
    (A : Matrix ι ι V5LaurentBase)
    (hA : ∀ z : ℂˣ, ∀ i, deriv (f i).val (z : ℂ) =
      ∑ j, arithmeticLaurentEvaluation z (A i j) * (f j).val (z : ℂ))
    [Algebra V5LaurentBase V5LaurentBase]
    [IsScalarTower AlgebraicComplex V5LaurentBase V5LaurentBase]
    (q : ℕ) (hq : 0 < q)
    (hpower : ∀ p, algebraMap V5LaurentBase V5LaurentBase p = v5LaurentPower q p)
    (hB : ∀ p : V5LaurentBase,
      algebraMap AlgebraicComplex ℂ
        (v5LaurentMark135 AlgebraicComplex (algebraMap V5LaurentBase V5LaurentBase p)) =
      v5WideSolutionEvaluation f (algebraMap V5LaurentBase (v5WideSolutionAlgebra f) p))
/-- The coefficient operator is inferred from the actual marked lift before
its pure-tensor rule is supplied. That literal rule identifies the actual
reversed derivative and gives the algebraic exponential endpoint internally.
Argument order after the fixed data is: a, c, hlift, hD; D is implicit. -/
def v5ActualScaledMarkedEndpoint136
    {D : V5LaurentBase ⊗[V5LaurentBase] v5WideSolutionAlgebra f →+
      V5LaurentBase ⊗[V5LaurentBase] v5WideSolutionAlgebra f} :=
  v5TensorMarkedOperatorEndpoint136 (D := D)
    (v5LaurentMark135 AlgebraicComplex) (v5WideSolutionEvaluation f) hB
    (v5ActualReversedSolutionKummerDifferential136 f A hA q hpower).toAddMonoidHom
    (v5ActualMarkedReverseEndpoint136 f hf A hA q hq hpower hB)
    (v5ActualScaledCoefficientDerivation_mul136 f A hA q hpower)
end StrictEUnit
#print axioms StrictEUnit.v5ActualScaledMarkedEndpoint136
