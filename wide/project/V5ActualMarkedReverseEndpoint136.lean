import V5ActualMarkedFirstOrderEndpoint136
import V5TensorMarkedReverseEndpoint136
import V5ReverseSolutionKummerDifferential136
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
local instance (priority := 7000) markedRightTensorModule136 {ι : Type}
    (f : ι → entireFunctionAlgebra) [Algebra V5LaurentBase V5LaurentBase] :
    Module AlgebraicComplex (v5WideSolutionAlgebra f ⊗[V5LaurentBase] V5LaurentBase) :=
  (solutionTensorCoefficientAlgebra136 f).toModule
local instance (priority := 7000) markedLeftTensorModule136 {ι : Type}
    (f : ι → entireFunctionAlgebra) [Algebra V5LaurentBase V5LaurentBase] :
    Module AlgebraicComplex (V5LaurentBase ⊗[V5LaurentBase] v5WideSolutionAlgebra f) :=
  (reversedSolutionCoefficientAlgebra136 f).toModule
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
/-- The explicit additive operator and its pure-tensor rule are supplied by
the actual solution-Kummer derivation, rather than assumed. -/
def v5ActualMarkedDifferentialEndpoint136 :=
  v5ActualMarkedFirstOrderEndpoint136 f hf A hA q hq hpower hB
    (v5ActualSolutionKummerDifferential136 f A hA q hpower).toAddMonoidHom
    (v5ActualSolutionKummerDifferential136_tmul f A hA q hpower)
/-- The coefficient-first actual formal first-order equation yields the
original marked algebraic exponential value. Commutation and the analytic
realization are derived internally, with no analytic ODE premise. -/
def v5ActualMarkedReverseEndpoint136 :=
  v5TensorMarkedReverseEndpoint136
    (v5LaurentMark135 AlgebraicComplex) (v5WideSolutionEvaluation f) hB
    (v5ActualReversedSolutionKummerDifferential136 f A hA q hpower).toAddMonoidHom
    (v5ActualSolutionKummerDifferential136 f A hA q hpower).toAddMonoidHom
    (v5ActualReversedSolutionKummerDifferential136_comm f A hA q hpower)
    (v5ActualMarkedDifferentialEndpoint136 f hf A hA q hq hpower hB)
end StrictEUnit
#print axioms StrictEUnit.v5ActualMarkedDifferentialEndpoint136
#print axioms StrictEUnit.v5ActualMarkedReverseEndpoint136
