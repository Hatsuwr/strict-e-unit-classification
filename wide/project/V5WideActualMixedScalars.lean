import V5WideActualMixedComparison
import V5WideOwnPVAction
import V5MixedRelativeCoaction
import V5MixedConstantsDescent
import V5MixedComparisonScalars

open scoped TensorProduct
open TensorProduct

noncomputable section
set_option maxHeartbeats 2500000
set_option maxRecDepth 1800
set_option synthInstance.maxHeartbeats 120000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule
attribute [-instance] HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing

namespace StrictEUnit
variable {r : ℕ}
    (f : Fin r → entireFunctionAlgebra)
    (A : Matrix (Fin r) (Fin r) V5LaurentBase)
    (hA : ∀ z : ℂˣ, ∀ i, deriv (f i).val (z : ℂ) =
      ∑ j, arithmeticLaurentEvaluation z (A i j) * (f j).val (z : ℂ))

def v5WideActualMixedDerivation104 :=
  mixedRelativeTensorDerivation v5LaurentBaseDerivation
    (v5WideFieldCandidateDerivation A) (v5WideSolutionDerivation f A hA)
    (v5WideFieldCandidate_base A) (v5WideSolution_base_compatible f A hA)

abbrev V5WideActualMixedConstants104 := derivationConstants (v5WideActualMixedDerivation104 f A hA)

def v5WideActualRelativeMixedMap104 :=
  v5MixedRelativeCoaction (S := v5WideSolutionAlgebra f) (v5WideOwnCoaction A)

theorem v5WideActualRelativeMixedMap104_differential
    (x : V5WideFieldCandidate A ⊗[V5LaurentBase] v5WideSolutionAlgebra f) :
    tensorDerivation (v5WideActualMixedDerivation104 f A hA)
        (v5WideActualRelativeMixedMap104 f A x) =
      v5WideActualRelativeMixedMap104 f A (v5WideActualMixedDerivation104 f A hA x) :=
  v5MixedRelativeCoaction_differential v5LaurentBaseDerivation
    (v5WideFieldCandidateDerivation A) (v5WideSolutionDerivation f A hA)
    (v5WideFieldCandidate_base A) (v5WideSolution_base_compatible f A hA)
    (v5WideOwnCoaction A) (v5WideOwnCoaction_differential A) x

theorem v5WideActualMixedComparison104_differential
    (x : V5WideFieldCandidate A ⊗[AlgebraicComplex] V5WideActualMixedConstants104 f A hA) :
    v5WideActualMixedDerivation104 f A hA (v5WideActualMixedComparison f A hA x) =
      v5WideActualMixedComparison f A hA (tensorDerivation (v5WideFieldCandidateDerivation A) x) :=
  v5_mixedConstantMultiplication_differential v5LaurentBaseDerivation
    (v5WideFieldCandidateDerivation A) (v5WideSolutionDerivation f A hA)
    (v5WideFieldCandidate_base A) (v5WideSolution_base_compatible f A hA) x

theorem v5WideActualMixedComparison104_bijective :
    Function.Bijective (v5MixedConstantMultiplication (v5WideActualMixedDerivation104 f A hA)) :=
  (v5WideActualMixedComparison f A hA).bijective

def v5WideActualMixedComparisonK :=
  v5MixedComparisonK (k := AlgebraicComplex) (B := V5LaurentBase)
    (R := V5WideFieldCandidate A) (S := v5WideSolutionAlgebra f)
    (v5WideActualMixedDerivation104 f A hA) (v5WideActualMixedComparison104_bijective f A hA)

theorem v5WideActualMixedComparisonK_differential
    (x : V5WideFieldCandidate A ⊗[AlgebraicComplex] V5WideActualMixedConstants104 f A hA) :
    v5WideActualMixedDerivation104 f A hA (v5WideActualMixedComparisonK f A hA x) =
      v5WideActualMixedComparisonK f A hA (tensorDerivation (v5WideFieldCandidateDerivation A) x) :=
  v5_mixedConstantMultiplication_differential v5LaurentBaseDerivation
    (v5WideFieldCandidateDerivation A) (v5WideSolutionDerivation f A hA)
    (v5WideFieldCandidate_base A) (v5WideSolution_base_compatible f A hA) x

end StrictEUnit
#print axioms StrictEUnit.v5WideActualRelativeMixedMap104_differential
#print axioms StrictEUnit.v5WideActualMixedComparison104_differential
#print axioms StrictEUnit.v5WideActualMixedComparison104_bijective
#print axioms StrictEUnit.v5WideActualMixedComparisonK
#print axioms StrictEUnit.v5WideActualMixedComparisonK_differential
