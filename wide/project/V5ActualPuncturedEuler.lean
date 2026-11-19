import V5PuncturedTensorDifferential
import V5LaurentBaseDerivation
import Mathlib.Analysis.Calculus.Deriv.ZPow

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing
open scoped TensorProduct
namespace StrictEUnit

/-- Actual analytic compatibility of the Laurent Euler operator. -/
theorem v5_laurent_punctured_euler {k : Type*} [Field k] (ι : k →+* ℂ)
    (p : LaurentPolynomial k) :
    V5HasPuncturedEuler (fun z => LaurentPolynomial.eval₂ ι z p)
      (fun z => LaurentPolynomial.eval₂ ι z (v5LaurentEulerLinear p)) := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    simpa only [map_add, Pi.add_apply] using hp.add hq
  | C_mul_T n a =>
    rw [← LaurentPolynomial.single_eq_C_mul_T, v5LaurentEulerLinear_single,
      LaurentPolynomial.single_eq_C_mul_T, LaurentPolynomial.single_eq_C_mul_T]
    refine ⟨fun z : ℂ => ι a * z^n, ?_, ?_⟩
    · intro z
      simp only [LaurentPolynomial.eval₂_C_mul_T, Units.val_zpow_eq_zpow_val]
    · intro z
      have hh := (hasDerivAt_zpow n (z : ℂ) (Or.inl (Units.ne_zero z))).const_mul (ι a)
      convert hh using 1
      simp only [LaurentPolynomial.eval₂_C_mul_T, map_mul, LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T, map_intCast,
        Units.val_zpow_eq_zpow_val]
      rw [zpow_sub₀ (Units.ne_zero z), zpow_one]
      ring

/-- Euler derivation of the literal solution algebra, not an abstract PV replacement. -/
def v5ActualSolutionEuler {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → entireFunctionAlgebra)
    (A : Matrix ι ι (LaurentPolynomial AlgebraicComplex))
    (hA : ∀ z : ℂˣ, ∀ i, deriv (f i).val (z : ℂ) =
      ∑ j, arithmeticLaurentEvaluation z (A i j) * (f j).val (z : ℂ)) :
    v5WideSolutionAlgebra f →+ v5WideSolutionAlgebra f where
  toFun s := v5WideSolutionParameter f true * v5WideSolutionDerivation f A hA s
  map_zero' := by rw [map_zero, mul_zero]
  map_add' x y := by rw [map_add, mul_add]

theorem v5ActualSolutionEuler_spec {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → entireFunctionAlgebra)
    (A : Matrix ι ι (LaurentPolynomial AlgebraicComplex))
    (hA : ∀ z : ℂˣ, ∀ i, deriv (f i).val (z : ℂ) =
      ∑ j, arithmeticLaurentEvaluation z (A i j) * (f j).val (z : ℂ))
    (s : v5WideSolutionAlgebra f) :
    V5HasPuncturedEuler s.val (v5ActualSolutionEuler f A hA s).val := by
  have hh := v5WideSolutionDerivative_spec f A hA s
  change V5HasPuncturedDeriv s.val _
  have he : (fun z : ℂˣ => (v5ActualSolutionEuler f A hA s).val z / (z : ℂ)) =
      (v5WideSolutionDerivative f A hA s).val := by
    funext z
    change ((z : ℂ) * (v5WideSolutionDerivative f A hA s).val z) / (z : ℂ) = _
    exact mul_div_cancel_left₀ _ (Units.ne_zero z)
  rw [he]
  exact hh

def v5LaurentPuncturedEvaluation {k : Type*} [Field k] (ι : k →+* ℂ) :
    LaurentPolynomial k →+* V5PuncturedFunctions where
  toFun p := fun z => LaurentPolynomial.eval₂ ι z p
  map_zero' := by funext z; exact map_zero _
  map_one' := by funext z; exact map_one _
  map_add' p q := by funext z; exact map_add _ _ _
  map_mul' p q := by funext z; exact map_mul _ _ _

/-- The actual S factor and literal Laurent factor have no remaining analytic
compatibility premises. Only the constructed tensor map/rule must be supplied. -/
theorem v5_actual_solution_laurent_tensor_euler
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → entireFunctionAlgebra)
    (A : Matrix ι ι (LaurentPolynomial AlgebraicComplex))
    (hA : ∀ z : ℂˣ, ∀ i, deriv (f i).val (z : ℂ) =
      ∑ j, arithmeticLaurentEvaluation z (A i j) * (f j).val (z : ℂ))
    {B : Type*} [CommRing B] [Algebra B (v5WideSolutionAlgebra f)]
    [Algebra B (LaurentPolynomial AlgebraicComplex)]
    (q : ℕ)
    (η : v5WideSolutionAlgebra f ⊗[B] LaurentPolynomial AlgebraicComplex →+* V5PuncturedFunctions)
    (Δ : v5WideSolutionAlgebra f ⊗[B] LaurentPolynomial AlgebraicComplex →+
      v5WideSolutionAlgebra f ⊗[B] LaurentPolynomial AlgebraicComplex)
    (hη : ∀ s d z, η (s ⊗ₜ[B] d) z = s.val (z^q) *
      LaurentPolynomial.eval₂ (algebraMap AlgebraicComplex ℂ) z d)
    (hΔ : ∀ s d, Δ (s ⊗ₜ[B] d) = (q • v5ActualSolutionEuler f A hA s) ⊗ₜ[B] d +
      s ⊗ₜ[B] v5LaurentEulerLinear d) :
    ∀ x, V5HasPuncturedEuler (η x) (η (Δ x)) := by
  exact v5_kummer_punctured_tensor_euler_transport q (v5WideSolutionAlgebra f).val.toRingHom
    (v5LaurentPuncturedEvaluation (algebraMap AlgebraicComplex ℂ)) η
    (v5ActualSolutionEuler f A hA) v5LaurentEulerLinear.toAddMonoidHom Δ hη hΔ
    (v5ActualSolutionEuler_spec f A hA) (v5_laurent_punctured_euler _)

end StrictEUnit
#print axioms StrictEUnit.v5_laurent_punctured_euler
#print axioms StrictEUnit.v5ActualSolutionEuler_spec

#print axioms StrictEUnit.v5_actual_solution_laurent_tensor_euler
