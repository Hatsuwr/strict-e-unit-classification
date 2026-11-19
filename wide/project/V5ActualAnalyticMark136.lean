import V5TensorCommutedMark136
import V5LaurentMark135
import V5MeromorphicZero
import V5WideSolutionRelativeBase
noncomputable section
open scoped TensorProduct
set_option Elab.async false
set_option maxHeartbeats 600000
set_option maxRecDepth 1800
set_option synthInstance.maxHeartbeats 20000
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing
namespace StrictEUnit
local instance analyticAlgebraSMulComm136 (U V Z : Type*)
    [CommRing U] [CommRing V] [CommRing Z] [Algebra U Z] [Algebra V Z] :
    SMulCommClass U V Z :=
  ⟨fun u v z => by simp only [Algebra.smul_def]; exact mul_left_comm _ _ _⟩
local instance (priority := 6000) analyticSolutionRing136 {ι : Type}
    (f : ι → entireFunctionAlgebra) : CommRing (v5WideSolutionAlgebra f) :=
  (v5WideSolutionAlgebra f).toCommRing
local instance (priority := 6000) analyticSolutionAddGroup136 {ι : Type}
    (f : ι → entireFunctionAlgebra) : AddCommGroup (v5WideSolutionAlgebra f) :=
  (v5WideSolutionAlgebra f).toCommRing.toAddCommGroup
local instance (priority := 6000) analyticSolutionAddMonoid136 {ι : Type}
    (f : ι → entireFunctionAlgebra) : AddCommMonoid (v5WideSolutionAlgebra f) :=
  (v5WideSolutionAlgebra f).toCommRing.toAddCommMonoid
local instance (priority := 6000) analyticSolutionCoefficientAlgebra136 {ι : Type}
    (f : ι → entireFunctionAlgebra) : Algebra AlgebraicComplex (v5WideSolutionAlgebra f) :=
  (v5WideSolutionAlgebra f).algebra
local instance (priority := 6000) analyticSolutionLaurentAlgebra136 {ι : Type}
    (f : ι → entireFunctionAlgebra) : Algebra V5LaurentBase (v5WideSolutionAlgebra f) :=
  v5WideSolutionLaurentAlgebra f
local instance (priority := 6000) analyticSolutionLaurentModule136 {ι : Type}
    (f : ι → entireFunctionAlgebra) : Module V5LaurentBase (v5WideSolutionAlgebra f) :=
  Algebra.toModule
/-- The literal analytic realization, after commuting tensor factors, has
exactly the existing marked tensor value. The conclusion is quantified over
all realizations, their pure-tensor formulas, and all tensor elements. -/
def v5ActualAnalyticMark136
    {ι : Type} (f : ι → entireFunctionAlgebra)
    [Algebra V5LaurentBase V5LaurentBase]
    [IsScalarTower AlgebraicComplex V5LaurentBase V5LaurentBase]
    (q : ℕ)
    (hB : ∀ p : V5LaurentBase,
      algebraMap AlgebraicComplex ℂ
        (v5LaurentMark135 AlgebraicComplex (algebraMap V5LaurentBase V5LaurentBase p)) =
      v5WideSolutionEvaluation f (algebraMap V5LaurentBase (v5WideSolutionAlgebra f) p)) :=
  v5RealizationCommutedMark136
    (k := AlgebraicComplex) (B := V5LaurentBase) (L := V5LaurentBase)
    (W := v5WideSolutionAlgebra f) (C := ℂ) (F := v5MeromorphicZeroAlgebra AlgebraicComplex)
    (I := ℂˣ) (v5LaurentMark135 AlgebraicComplex) (v5WideSolutionEvaluation f) hB
    (fun s z => s.val z) (fun d z => arithmeticLaurentEvaluation z d)
    (fun z => v5FunctionSubalgebraEval136 (v5MeromorphicZeroAlgebra AlgebraicComplex) z)
    (fun _ => rfl)
    (fun d => (v5LaurentMark_map135 (algebraMap AlgebraicComplex ℂ) d).symm) q
/-- The same comparison specializes to the inverse of every unit. -/
def v5ActualAnalyticInverseMark136
    {ι : Type} (f : ι → entireFunctionAlgebra)
    [Algebra V5LaurentBase V5LaurentBase]
    [IsScalarTower AlgebraicComplex V5LaurentBase V5LaurentBase]
    (q : ℕ)
    (hB : ∀ p : V5LaurentBase,
      algebraMap AlgebraicComplex ℂ
        (v5LaurentMark135 AlgebraicComplex (algebraMap V5LaurentBase V5LaurentBase p)) =
      v5WideSolutionEvaluation f (algebraMap V5LaurentBase (v5WideSolutionAlgebra f) p)) :=
  v5RealizationCommutedInverseMark136
    (k := AlgebraicComplex) (B := V5LaurentBase) (L := V5LaurentBase)
    (W := v5WideSolutionAlgebra f) (C := ℂ) (F := v5MeromorphicZeroAlgebra AlgebraicComplex)
    (I := ℂˣ) (v5LaurentMark135 AlgebraicComplex) (v5WideSolutionEvaluation f) hB
    (fun s z => s.val z) (fun d z => arithmeticLaurentEvaluation z d)
    (fun z => v5FunctionSubalgebraEval136 (v5MeromorphicZeroAlgebra AlgebraicComplex) z)
    (fun _ => rfl)
    (fun d => (v5LaurentMark_map135 (algebraMap AlgebraicComplex ℂ) d).symm) q
end StrictEUnit
#print axioms StrictEUnit.v5ActualAnalyticMark136
#print axioms StrictEUnit.v5ActualAnalyticInverseMark136
