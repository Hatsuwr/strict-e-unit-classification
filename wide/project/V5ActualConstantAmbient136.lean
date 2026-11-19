import V5ConstantAmbientCharacter136
import V5ActualQuotientCharacter135
noncomputable section
set_option maxHeartbeats 600000
set_option maxRecDepth 1800
set_option synthInstance.maxHeartbeats 45000
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing
namespace StrictEUnit
local instance : IsAlgClosed AlgebraicComplex := IsAlgClosure.isAlgClosed ℚ
variable {r : ℕ} (f : Fin r → entireFunctionAlgebra)
  (A : Matrix (Fin r) (Fin r) V5LaurentBase)
  (hf : ∀ i, V5IsBroadEFunction (f i).val)
  (hA : ∀ z : ℂˣ, ∀ i, deriv (f i).val (z : ℂ) =
    ∑ j, arithmeticLaurentEvaluation z (A i j) * (f j).val (z : ℂ))
def v5ActualConstantAmbientCharacter136 :=
  v5ConstantAmbientCharacter136
    (v5WideFieldCandidateDerivation A) (v5WideActualMixedDerivation104 f A hA)
    (v5WideOwnDerivation_constants A) (v5WideActualMixedComparison104_bijective f A hA)
    (v5WideActualMixedComparisonK_differential f A hA)
    (v5WideOwnCoaction A) (v5WideActualRelativeMixedMap104_differential f A hA)
    (v5GenericOwnIdentity123 A) _ _ _ (v5ActualQuotientCharacter135 f A hf hA)
def v5ActualConstantAmbientReciprocal136 (i j : Fin r)
    (hij : (f i).val 1 * (f j).val 1 = 1) :=
  (v5ActualConstantAmbientCharacter136 f A hf hA)
    (v5WideMixedConstantUnit f A hf hA i j hij)
end StrictEUnit
#print axioms StrictEUnit.v5ActualConstantAmbientCharacter136
#print axioms StrictEUnit.v5ActualConstantAmbientReciprocal136
