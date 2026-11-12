import Stage20ArithmeticFrameLifting
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral

/-! Genuine entire polynomial-relation residuals and analytic continuation.
No relation-lifting theorem is assumed in this module. -/
noncomputable section
open scoped Topology
namespace StrictEUnit

/-- Algebraic numbers as constant actual entire functions. -/
def stage35_entireCoefficient : AlgebraicComplex →+* entireFunctionAlgebra :=
  (algebraMap ℂ entireFunctionAlgebra).comp (algebraicClosure ℚ ℂ).val.toRingHom

/-- The concrete substituted polynomial, defined on the whole complex plane. -/
def stage35_relationResidual {ι : Type*} (f : ι → entireFunctionAlgebra)
    (H : Polynomial (MvPolynomial ι AlgebraicComplex)) (z : ℂ) : ℂ :=
  Polynomial.eval₂ (MvPolynomial.eval₂Hom (algebraicClosure ℚ ℂ).val.toRingHom
    (fun i => (f i).val z)) z H

/-- The same residual constructed in the ring of actual entire functions. -/
def stage35_entireRelationResidual {ι : Type*} (f : ι → entireFunctionAlgebra)
    (H : Polynomial (MvPolynomial ι AlgebraicComplex)) : entireFunctionAlgebra :=
  Polynomial.eval₂ (MvPolynomial.eval₂Hom stage35_entireCoefficient f) entireCoordinate H

@[simp] theorem stage35_entireRelationResidual_apply {ι : Type*}
    (f : ι → entireFunctionAlgebra) (H : Polynomial (MvPolynomial ι AlgebraicComplex))
    (z : ℂ) :
    (stage35_entireRelationResidual f H).val z = stage35_relationResidual f H z := by
  change (entireEvaluation z).toRingHom
    (Polynomial.eval₂ (MvPolynomial.eval₂Hom stage35_entireCoefficient f)
      entireCoordinate H) = _
  rw [Polynomial.hom_eval₂, MvPolynomial.comp_eval₂Hom]
  rfl

/-- A genuine entire function vanishing on a neighborhood of 1 vanishes globally. -/
theorem stage35_entire_zero_of_local (g : entireFunctionAlgebra)
    (h : g.val =ᶠ[𝓝 (1 : ℂ)] 0) : ∀ z, g.val z = 0 := by
  have hg : AnalyticOnNhd ℂ g.val Set.univ :=
    g.property.differentiableOn.analyticOnNhd isOpen_univ
  have heq : g.val = 0 := hg.eq_of_eventuallyEq analyticOnNhd_const h
  intro z
  exact congrFun heq z

/-- A local polynomial relation among entire functions is a global relation. -/
theorem stage35_relation_zero_of_local {ι : Type*} (f : ι → entireFunctionAlgebra)
    (H : Polynomial (MvPolynomial ι AlgebraicComplex))
    (h : stage35_relationResidual f H =ᶠ[𝓝 (1 : ℂ)] 0) :
    ∀ z, stage35_relationResidual f H z = 0 := by
  have hg : (stage35_entireRelationResidual f H).val =ᶠ[𝓝 (1 : ℂ)] 0 := by
    filter_upwards [h] with z hz
    simpa only [stage35_entireRelationResidual_apply] using hz
  simpa only [stage35_entireRelationResidual_apply] using
    stage35_entire_zero_of_local (stage35_entireRelationResidual f H) hg

end StrictEUnit
