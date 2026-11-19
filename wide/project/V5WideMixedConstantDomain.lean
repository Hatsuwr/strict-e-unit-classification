import V5WideMixedConstantUnit
import Mathlib.Algebra.Ring.Hom.Basic

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

/-- The actual marked-fiber evaluation embeds mixed constants into ℂ. -/
theorem v5WideMixedConstantEvaluation_injective :
    Function.Injective (v5WideMixedConstantEvaluation f A hf hA) :=
  (v5WideSolutionFiberEvaluation_injective f A hf hA).comp
    (v5WideActualExactFiber f A hA).injective

/-- The mixed horizontal constant algebra is a domain. This does not assert
that the own-PV Hopf algebra H is a domain or connected. -/
def v5WideMixedConstantDomain :=
  Function.Injective.isDomain (v5WideMixedConstantEvaluation f A hf hA).toRingHom
    (v5WideMixedConstantEvaluation_injective f A hf hA)

/-- Nontriviality of the same actual mixed constant algebra. -/
def v5WideMixedConstantNontrivial :=
  (v5WideMixedConstantDomain f A hf hA).toNontrivial

end StrictEUnit
#print axioms StrictEUnit.v5WideMixedConstantEvaluation_injective
#print axioms StrictEUnit.v5WideMixedConstantDomain
#print axioms StrictEUnit.v5WideMixedConstantNontrivial
#check StrictEUnit.v5WideMixedConstantDomain
