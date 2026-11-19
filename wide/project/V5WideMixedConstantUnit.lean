import V5WideActualExactFiber
import V5UnitTransport

open scoped TensorProduct
noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 1800
set_option synthInstance.maxHeartbeats 30000
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing
namespace StrictEUnit
variable {r : ℕ} (f : Fin r → entireFunctionAlgebra)
    (A : Matrix (Fin r) (Fin r) V5LaurentBase)
    (hf : ∀ i, V5IsBroadEFunction (f i).val)
    (hA : ∀ z : ℂˣ, ∀ i, deriv (f i).val (z : ℂ) =
      ∑ j, arithmeticLaurentEvaluation z (A i j) * (f j).val (z : ℂ))

/-- Evaluate mixed horizontal constants through the actual mark and exact
fiber. This map is not an identification with the own-PV Hopf algebra. -/
def v5WideMixedConstantEvaluation :=
  v5TransportEvaluation (k := AlgebraicComplex) (v5WideActualExactFiber f A hA)
    (v5WideSolutionFiberEvaluation f A hf hA)

/-- Transport the actual reciprocal fiber unit into actual mixed constants.
No coaction, connectedness or global functional unit is assumed. -/
def v5WideMixedConstantUnit (i j : Fin r)
    (hij : (f i).val 1 * (f j).val 1 = 1) :=
  v5UnitTransport (k := AlgebraicComplex) (v5WideActualExactFiber f A hA)
    (v5WideSolutionFiberUnit f A hf hA i j hij)

@[simp] theorem v5WideMixedConstantUnit_value (i j : Fin r)
    (hij : (f i).val 1 * (f j).val 1 = 1) :
    v5WideMixedConstantEvaluation f A hf hA
      (v5WideMixedConstantUnit f A hf hA i j hij).val = (f i).val 1 :=
  v5UnitTransport_value (k := AlgebraicComplex) (v5WideActualExactFiber f A hA)
    (v5WideSolutionFiberEvaluation f A hf hA) (v5WideSolutionFiberUnit f A hf hA i j hij)

@[simp] theorem v5WideMixedConstantUnit_inverse_value (i j : Fin r)
    (hij : (f i).val 1 * (f j).val 1 = 1) :
    v5WideMixedConstantEvaluation f A hf hA
      (v5WideMixedConstantUnit f A hf hA i j hij).inv = (f j).val 1 :=
  v5UnitTransport_inverse_value (k := AlgebraicComplex) (v5WideActualExactFiber f A hA)
    (v5WideSolutionFiberEvaluation f A hf hA) (v5WideSolutionFiberUnit f A hf hA i j hij)

end StrictEUnit
#print axioms StrictEUnit.v5WideMixedConstantEvaluation
#print axioms StrictEUnit.v5WideMixedConstantUnit
#print axioms StrictEUnit.v5WideMixedConstantUnit_value
#print axioms StrictEUnit.v5WideMixedConstantUnit_inverse_value
