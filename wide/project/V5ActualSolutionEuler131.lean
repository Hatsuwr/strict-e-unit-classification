import V5ActualPuncturedEuler
import V5WideSolutionBaseDifferential
import V5WideSolutionRelativeBase

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing
namespace StrictEUnit
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (f : ι → entireFunctionAlgebra)
variable (A : Matrix ι ι V5LaurentBase)
variable (hA : ∀ z : ℂˣ, ∀ i, deriv (f i).val (z : ℂ) =
  ∑ j, arithmeticLaurentEvaluation z (A i j) * (f j).val (z : ℂ))

def v5ScaleSubalgebraDerivation131 {k R : Type*} [CommRing k] [CommRing R]
    [Algebra k R] (S : Subalgebra k R) (a : S) (d : Derivation k S S) :
    Derivation k S S := a • d

def v5ActualSolutionEulerDerivation131 :=
  v5ScaleSubalgebraDerivation131 (v5WideSolutionAlgebra f)
    (v5WideSolutionParameter f true) (v5WideSolutionDerivation f A hA)

theorem v5ActualSolutionEulerDerivation131_apply (s : v5WideSolutionAlgebra f) :
    v5ActualSolutionEulerDerivation131 f A hA s = v5ActualSolutionEuler f A hA s := rfl

theorem v5ActualSolutionEuler131_base (p : V5LaurentBase) :
    v5ActualSolutionEuler f A hA (v5WideSolutionBase f p) =
      v5WideSolutionBase f (v5LaurentEulerLinear p) := by
  change v5WideSolutionParameter f true * v5WideSolutionDerivation f A hA _ = _
  rw [v5WideSolution_base_compatible]
  have ht : v5WideSolutionBase f (LaurentPolynomial.T 1) =
      v5WideSolutionParameter f true := by
    change LaurentPolynomial.eval₂ _ (v5WideSolutionCoordinate f) _ = _
    rw [LaurentPolynomial.eval₂_T, zpow_one]
    rfl
  rw [← ht, ← map_mul]
  congr 1
  change LaurentPolynomial.T 1 * (LaurentPolynomial.T (-1) * v5LaurentEulerLinear p) = _
  rw [← mul_assoc, ← LaurentPolynomial.T_add]
  norm_num

end StrictEUnit
#print axioms StrictEUnit.v5ActualSolutionEulerDerivation131
#print axioms StrictEUnit.v5ActualSolutionEulerDerivation131_apply
#print axioms StrictEUnit.v5ActualSolutionEuler131_base

namespace StrictEUnit
theorem v5ActualSolutionEulerDerivation131_base
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → entireFunctionAlgebra)
    (A : Matrix ι ι V5LaurentBase)
    (hA : ∀ z : ℂˣ, ∀ i, deriv (f i).val (z : ℂ) =
      ∑ j, arithmeticLaurentEvaluation z (A i j) * (f j).val (z : ℂ))
    (p : V5LaurentBase) :
    v5ActualSolutionEulerDerivation131 f A hA (algebraMap V5LaurentBase
      (v5WideSolutionAlgebra f) p) =
    algebraMap V5LaurentBase (v5WideSolutionAlgebra f) (v5LaurentEulerLinear p) :=
  v5ActualSolutionEuler131_base f A hA p
end StrictEUnit
#print axioms StrictEUnit.v5ActualSolutionEulerDerivation131_base
