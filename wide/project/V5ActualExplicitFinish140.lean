import V5ActualScaledMarkedEndpoint136
noncomputable section
open scoped TensorProduct
set_option Elab.async false
set_option maxHeartbeats 800000
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
/-- Pass the explicit bundled operator and its rule before the marked
existential, while preserving the endpoint's already elaborated predicate. -/
def v5OperatorRuleFirstFinish140
    {X C : Type*} [AddMonoid X]
    {Rule : (X →+ X) → Prop} {Lift : (X →+ X) → C → C → Prop}
    {Q : C → C → Prop}
    (hend : ∀ (D : X →+ X) (a c : C), Lift D a c → Rule D → Q a c)
    (D : X →+ X) (hD : Rule D) (a c : C) (hlift : Lift D a c) : Q a c :=
  hend D a c hlift hD
/-- Actual analytic callback, retaining the checked predicate from136.
Arguments after fixed data are D, its tensor rule, a, c, marked lift. -/
def v5ActualExplicitAddFinish140 :=
  v5OperatorRuleFirstFinish140
    (fun D => v5ActualScaledMarkedEndpoint136 (D := D) f hf A hA q hq hpower hB)
end StrictEUnit
#print axioms StrictEUnit.v5OperatorRuleFirstFinish140
#print axioms StrictEUnit.v5ActualExplicitAddFinish140
