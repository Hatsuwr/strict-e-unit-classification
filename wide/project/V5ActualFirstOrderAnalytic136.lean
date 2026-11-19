import V5AlgebraicExponentialMark
import V5ActualPuncturedEuler
noncomputable section
open scoped TensorProduct
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1600
set_option synthInstance.maxHeartbeats 80000
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing
namespace StrictEUnit
/-- The same actual meromorphic realization supports arithmetic normalization
and the tensor Euler rule. A formal first-order equation therefore gives an
algebraic exponential mark without an extra analytic ODE premise. -/
theorem v5_actual_first_order_analytic136
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → entireFunctionAlgebra)
    (hf : ∀ i, V5IsBroadEFunction (f i).val)
    (A : Matrix ι ι V5LaurentBase)
    (hA : ∀ z : ℂˣ, ∀ i, deriv (f i).val (z : ℂ) =
      ∑ j, arithmeticLaurentEvaluation z (A i j) * (f j).val (z : ℂ))
    [Algebra V5LaurentBase V5LaurentBase]
    (q : ℕ) (hq : 0 < q)
    (hpower : ∀ p, algebraMap V5LaurentBase V5LaurentBase p = v5LaurentPower q p)
    (Δ : v5WideSolutionAlgebra f ⊗[V5LaurentBase] V5LaurentBase →+
      v5WideSolutionAlgebra f ⊗[V5LaurentBase] V5LaurentBase)
    (hΔ : ∀ s d, Δ (s ⊗ₜ[V5LaurentBase] d) =
      (q • v5ActualSolutionEuler f A hA s) ⊗ₜ[V5LaurentBase] d +
        s ⊗ₜ[V5LaurentBase] v5LaurentEulerLinear d) :
    ∃ η : v5WideSolutionAlgebra f ⊗[V5LaurentBase] V5LaurentBase →+*
        v5MeromorphicZeroAlgebra AlgebraicComplex,
      (∀ s d z, (η (s ⊗ₜ[V5LaurentBase] d)).val z =
        s.val (z^q) * arithmeticLaurentEvaluation z d) ∧
      ∀ u : v5WideSolutionAlgebra f ⊗[V5LaurentBase] V5LaurentBase, IsUnit u →
        ∀ L : V5LaurentBase,
          Δ u = ((1 : v5WideSolutionAlgebra f) ⊗ₜ[V5LaurentBase] L) * u →
          ∃ α β : AlgebraicComplex, α ≠ 0 ∧
            (η u).val 1 = (α : ℂ) * Complex.exp (β : ℂ) := by
  obtain ⟨η, hη, hend⟩ := v5_actual_wide_kummer_laurent_ode_mark f hf q hq
    (RingHom.id V5LaurentBase) hpower
  let η' := (v5MeromorphicZeroAlgebra AlgebraicComplex).val.toRingHom.comp η
  have hE : ∀ x, V5HasPuncturedEuler (η x).val (η (Δ x)).val :=
    v5_actual_solution_laurent_tensor_euler f A hA q η' Δ hη hΔ
  refine ⟨η, hη, ?_⟩
  intro u hu L hODE
  let du : V5PuncturedFunctions := fun z => (η (Δ u)).val z / (z : ℂ)
  have hd : V5HasPuncturedDeriv (η u).val du := hE u
  have hval (z : ℂˣ) :
      (η (Δ u)).val z = arithmeticLaurentEvaluation z L * (η u).val z := by
    rw [hODE, η.map_mul]
    change (η ((1 : v5WideSolutionAlgebra f) ⊗ₜ[V5LaurentBase] L)).val z *
      (η u).val z = _
    rw [hη]
    change (1 : ℂ) * arithmeticLaurentEvaluation z L * (η u).val z = _
    rw [one_mul]
  apply hend u hu du L hd
  intro z
  change (z : ℂ) * ((η (Δ u)).val z / (z : ℂ)) = _
  rw [mul_div_cancel₀ _ (Units.ne_zero z), hval]
end StrictEUnit
#print axioms StrictEUnit.v5_actual_first_order_analytic136
