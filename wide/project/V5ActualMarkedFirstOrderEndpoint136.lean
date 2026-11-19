import V5TensorMarkedExponentialEndpoint136
import V5ActualAnalyticMark136
import V5ActualFirstOrderAnalytic136
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
local instance endpointAlgebraSMulComm136 (U V Z : Type*)
    [CommRing U] [CommRing V] [CommRing Z] [Algebra U Z] [Algebra V Z] :
    SMulCommClass U V Z :=
  ⟨fun u v z => by simp only [Algebra.smul_def]; exact mul_left_comm _ _ _⟩
local instance (priority := 6000) endpointSolutionRing136 {ι : Type}
    (f : ι → entireFunctionAlgebra) : CommRing (v5WideSolutionAlgebra f) :=
  (v5WideSolutionAlgebra f).toCommRing
local instance (priority := 6000) endpointSolutionAddGroup136 {ι : Type}
    (f : ι → entireFunctionAlgebra) : AddCommGroup (v5WideSolutionAlgebra f) :=
  (v5WideSolutionAlgebra f).toCommRing.toAddCommGroup
local instance (priority := 6000) endpointSolutionAddMonoid136 {ι : Type}
    (f : ι → entireFunctionAlgebra) : AddCommMonoid (v5WideSolutionAlgebra f) :=
  (v5WideSolutionAlgebra f).toCommRing.toAddCommMonoid
local instance (priority := 6000) endpointSolutionCoefficientAlgebra136 {ι : Type}
    (f : ι → entireFunctionAlgebra) : Algebra AlgebraicComplex (v5WideSolutionAlgebra f) :=
  (v5WideSolutionAlgebra f).algebra
local instance (priority := 6000) endpointSolutionLaurentAlgebra136 {ι : Type}
    (f : ι → entireFunctionAlgebra) : Algebra V5LaurentBase (v5WideSolutionAlgebra f) :=
  v5WideSolutionLaurentAlgebra f
local instance (priority := 6000) endpointSolutionLaurentModule136 {ι : Type}
    (f : ι → entireFunctionAlgebra) : Module V5LaurentBase (v5WideSolutionAlgebra f) :=
  Algebra.toModule
/-- The actual reciprocal tensor lift yields an algebraic exponential mark
once its commuted unit satisfies the formal first-order Euler equation.
The analytic realization and analytic ODE are consequences, not premises. -/
def v5ActualMarkedFirstOrderEndpoint136
    {ι : Type} [Fintype ι] [DecidableEq ι]
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
    (Δ : v5WideSolutionAlgebra f ⊗[V5LaurentBase] V5LaurentBase →+
      v5WideSolutionAlgebra f ⊗[V5LaurentBase] V5LaurentBase)
    (hΔ : ∀ s d, Δ (s ⊗ₜ[V5LaurentBase] d) =
      (q • v5ActualSolutionEuler f A hA s) ⊗ₜ[V5LaurentBase] d +
        s ⊗ₜ[V5LaurentBase] v5LaurentEulerLinear d) := by
  letI : CommRing (v5WideSolutionAlgebra f) := (v5WideSolutionAlgebra f).toCommRing
  letI : AddCommGroup (v5WideSolutionAlgebra f) := (v5WideSolutionAlgebra f).toCommRing.toAddCommGroup
  letI : AddCommMonoid (v5WideSolutionAlgebra f) := (v5WideSolutionAlgebra f).toCommRing.toAddCommMonoid
  letI : Algebra AlgebraicComplex (v5WideSolutionAlgebra f) := (v5WideSolutionAlgebra f).algebra
  letI : Algebra V5LaurentBase (v5WideSolutionAlgebra f) := v5WideSolutionLaurentAlgebra f
  letI : Module V5LaurentBase (v5WideSolutionAlgebra f) := Algebra.toModule
  exact v5TensorMarkedExponentialEndpoint136
    (v5LaurentMark135 AlgebraicComplex) (v5WideSolutionEvaluation f) hB Δ
    (v5FunctionSubalgebraEval136 (v5MeromorphicZeroAlgebra AlgebraicComplex) (1 : ℂˣ))
    (algebraMap AlgebraicComplex ℂ) (fun β : AlgebraicComplex => Complex.exp (β : ℂ))
    (fun η => ∀ (s : v5WideSolutionAlgebra f) (d : V5LaurentBase) (z : ℂˣ),
      (η (s ⊗ₜ[V5LaurentBase] d)).val z = s.val (z^q) * arithmeticLaurentEvaluation z d)
    (v5_actual_first_order_analytic136 f hf A hA q hq hpower Δ hΔ)
    (v5ActualAnalyticMark136 f q hB)
end StrictEUnit
#print axioms StrictEUnit.v5ActualMarkedFirstOrderEndpoint136
