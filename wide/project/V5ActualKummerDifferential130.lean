import V5KummerBalancedAnalytic
import V5ActualPuncturedEuler
import V5ActualKummerFunctions

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
attribute [-instance] HahnSeries.instModule HahnSeries.instSMul
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing
open scoped TensorProduct
namespace StrictEUnit

/-- Actual solution and literal Laurent factors, with the meromorphic map constructed
rather than assumed. The additive tensor Euler operator and its pure-tensor rule
remain inputs; all factor analytic and finite-pole premises are discharged. -/
theorem v5_actual_kummer_differential130
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → entireFunctionAlgebra)
    (A : Matrix ι ι V5LaurentBase)
    (hA : ∀ z : ℂˣ, ∀ i, deriv (f i).val (z : ℂ) =
      ∑ j, arithmeticLaurentEvaluation z (A i j) * (f j).val (z : ℂ))
    [Algebra V5LaurentBase V5LaurentBase]
    (q : ℕ)
    (Δ : v5WideSolutionAlgebra f ⊗[V5LaurentBase] V5LaurentBase →+
      v5WideSolutionAlgebra f ⊗[V5LaurentBase] V5LaurentBase)
    (hΔ : ∀ s d, Δ (s ⊗ₜ[V5LaurentBase] d) =
      (q • v5ActualSolutionEuler f A hA s) ⊗ₜ[V5LaurentBase] d +
      s ⊗ₜ[V5LaurentBase] v5LaurentEulerLinear d)
    (hpower : ∀ p, algebraMap V5LaurentBase V5LaurentBase p = v5LaurentPower q p) :
    ∃ (η : v5WideSolutionAlgebra f ⊗[V5LaurentBase] V5LaurentBase →+*
        v5MeromorphicZeroAlgebra AlgebraicComplex),
      (∀ s d z, (η (s ⊗ₜ[V5LaurentBase] d)).val z =
        s.val (z^q) * arithmeticLaurentEvaluation z d) ∧
      (∀ x, V5HasPuncturedEuler (η x).val (η (Δ x)).val) := by
  obtain ⟨η, hη, hm⟩ := v5_actual_kummer_punctured_realization f q
    (RingHom.id V5LaurentBase) hpower
  refine ⟨η, hη, ?_⟩
  let η' := (v5MeromorphicZeroAlgebra AlgebraicComplex).val.toRingHom.comp η
  exact v5_actual_solution_laurent_tensor_euler f A hA q η' Δ hη hΔ

end StrictEUnit
#print axioms StrictEUnit.v5_actual_kummer_differential130
