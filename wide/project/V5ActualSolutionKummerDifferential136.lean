import V5PowerEuler133
import V5ScaledBalancedTensor
noncomputable section
open scoped TensorProduct
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 1800
set_option synthInstance.maxHeartbeats 15000
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing
namespace StrictEUnit
local instance solutionAlgebraSMulComm136 (U V Z : Type*) [CommRing U] [CommRing V]
    [CommRing Z] [Algebra U Z] [Algebra V Z] : SMulCommClass U V Z :=
  ⟨fun u v z => by simp only [Algebra.smul_def]; exact mul_left_comm _ _ _⟩
variable {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → entireFunctionAlgebra) (A : Matrix ι ι V5LaurentBase)
    (hA : ∀ z : ℂˣ, ∀ i, deriv (f i).val (z : ℂ) =
      ∑ j, arithmeticLaurentEvaluation z (A i j) * (f j).val (z : ℂ))
    [Algebra V5LaurentBase V5LaurentBase]
    (q : ℕ)
    (hpower : ∀ p, algebraMap V5LaurentBase V5LaurentBase p = v5LaurentPower q p)
local instance (priority := 6000) solutionRing136 : CommRing (v5WideSolutionAlgebra f) :=
  (v5WideSolutionAlgebra f).toCommRing
local instance (priority := 6000) solutionAddGroup136 : AddCommGroup (v5WideSolutionAlgebra f) :=
  (v5WideSolutionAlgebra f).toCommRing.toAddCommGroup
local instance (priority := 6000) solutionAddMonoid136 : AddCommMonoid (v5WideSolutionAlgebra f) :=
  (v5WideSolutionAlgebra f).toCommRing.toAddCommMonoid
local instance (priority := 6000) solutionCoefficientAlgebra136 :
    Algebra AlgebraicComplex (v5WideSolutionAlgebra f) := (v5WideSolutionAlgebra f).algebra
local instance (priority := 6000) solutionLaurentAlgebra136 :
    Algebra V5LaurentBase (v5WideSolutionAlgebra f) := v5WideSolutionLaurentAlgebra f
local instance (priority := 6000) solutionLaurentModule136 :
    Module V5LaurentBase (v5WideSolutionAlgebra f) := Algebra.toModule
local instance (priority := 6000) solutionTensorCoefficientAlgebra136 :
    Algebra AlgebraicComplex (v5WideSolutionAlgebra f ⊗[V5LaurentBase] V5LaurentBase) :=
  @Algebra.TensorProduct.leftAlgebra V5LaurentBase AlgebraicComplex
    (v5WideSolutionAlgebra f) V5LaurentBase inferInstance
    (solutionRing136 f).toSemiring (solutionLaurentAlgebra136 f)
    inferInstance inferInstance inferInstance (solutionCoefficientAlgebra136 f)
    (solutionAlgebraSMulComm136 V5LaurentBase AlgebraicComplex (v5WideSolutionAlgebra f))
/-- Genuine solution-Kummer derivation, with the necessary q scaling derived
from the actual power-map identity. -/
def v5ActualSolutionKummerDifferential136 := by
  let hS : ∀ b : V5LaurentBase,
      v5ActualSolutionEulerDerivation131 f A hA
        (algebraMap V5LaurentBase (v5WideSolutionAlgebra f) b) =
      algebraMap V5LaurentBase (v5WideSolutionAlgebra f) (v5BaseEuler132 b) := by
    intro b
    rw [v5BaseEuler132_apply]
    exact v5ActualSolutionEulerDerivation131_base f A hA b
  let hL : ∀ b : V5LaurentBase,
      v5BaseEuler132 (algebraMap V5LaurentBase V5LaurentBase b) =
        q • algebraMap V5LaurentBase V5LaurentBase (v5BaseEuler132 b) := by
    intro b
    rw [hpower, hpower]
    simpa only [v5BaseEuler132_apply] using v5PowerEuler133 q b
  exact v5ScaledBalancedTensorDerivation129 v5BaseEuler132
    (v5ActualSolutionEulerDerivation131 f A hA) v5BaseEuler132 q hS hL (fun _ => rfl)

theorem v5ActualSolutionKummerDifferential136_tmul
    (s : v5WideSolutionAlgebra f) (l : V5LaurentBase) :
    v5ActualSolutionKummerDifferential136 f A hA q hpower (s ⊗ₜ[V5LaurentBase] l) =
      (q • v5ActualSolutionEuler f A hA s) ⊗ₜ[V5LaurentBase] l +
        s ⊗ₜ[V5LaurentBase] v5LaurentEulerLinear l := by
  unfold v5ActualSolutionKummerDifferential136
  rw [v5ScaledBalancedTensorDerivation129_tmul]
  simp only [v5ActualSolutionEulerDerivation131_apply, v5BaseEuler132_apply]
end StrictEUnit
#print axioms StrictEUnit.v5ActualSolutionKummerDifferential136
#print axioms StrictEUnit.v5ActualSolutionKummerDifferential136_tmul
