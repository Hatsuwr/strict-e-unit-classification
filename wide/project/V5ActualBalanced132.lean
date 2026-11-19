import V5ActualSolutionEuler131
import V5ScaledBalancedTensor


noncomputable section
open scoped TensorProduct
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
attribute [-instance] HahnSeries.instModule HahnSeries.instSMul
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing
namespace StrictEUnit

def v5BaseEuler132 {K : Type*} [Field K] :
    Derivation K (LaurentPolynomial K) (LaurentPolynomial K) :=
  (LaurentPolynomial.T 1 : LaurentPolynomial K) • (v5LaurentBaseDerivation : Derivation K (LaurentPolynomial K) (LaurentPolynomial K))

theorem v5BaseEuler132_apply {K : Type*} [Field K] (p : LaurentPolynomial K) :
    v5BaseEuler132 p = v5LaurentEulerLinear p := by
  change LaurentPolynomial.T 1 * (LaurentPolynomial.T (-1) * v5LaurentEulerLinear p) = _
  rw [← mul_assoc, ← LaurentPolynomial.T_add]
  norm_num

theorem v5ActualSolutionBalanced132
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → entireFunctionAlgebra)
    (A : Matrix ι ι V5LaurentBase)
    (hA : ∀ z : ℂˣ, ∀ i, deriv (f i).val (z : ℂ) =
      ∑ j, arithmeticLaurentEvaluation z (A i j) * (f j).val (z : ℂ))
    {D : Type*} [CommRing D] [Algebra AlgebraicComplex D] [Algebra V5LaurentBase D]
    (dD : Derivation AlgebraicComplex D D) (q : ℕ)
    (hD : ∀ b : V5LaurentBase, dD (algebraMap V5LaurentBase D b) =
      q • algebraMap V5LaurentBase D (v5LaurentEulerLinear b)) :
    ∀ b : V5LaurentBase,
      (q • v5ActualSolutionEuler f A hA (algebraMap V5LaurentBase (v5WideSolutionAlgebra f) b))
        ⊗ₜ[V5LaurentBase] (1 : D) =
      (1 : v5WideSolutionAlgebra f) ⊗ₜ[V5LaurentBase] dD (algebraMap V5LaurentBase D b) := by
  apply v5_scaled_tensor_balance129 v5BaseEuler132
    (v5ActualSolutionEulerDerivation131 f A hA) dD q
  · intro b
    rw [v5BaseEuler132_apply]
    exact v5ActualSolutionEulerDerivation131_base f A hA b
  · intro b
    rw [v5BaseEuler132_apply]
    exact hD b


def v5NatScaleDerivation132 {k S : Type*} [CommRing k] [CommRing S] [Algebra k S]
    (q : ℕ) (d : Derivation k S S) := q • d

theorem v5ActualSolutionTensorEuler132
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → entireFunctionAlgebra)
    (A : Matrix ι ι V5LaurentBase)
    (hA : ∀ z : ℂˣ, ∀ i, deriv (f i).val (z : ℂ) =
      ∑ j, arithmeticLaurentEvaluation z (A i j) * (f j).val (z : ℂ))
    {D : Type*} [CommRing D] [Algebra AlgebraicComplex D] [Algebra V5LaurentBase D]
    (dD : Derivation AlgebraicComplex D D) (q : ℕ)
    (hD : ∀ b : V5LaurentBase, dD (algebraMap V5LaurentBase D b) =
      q • algebraMap V5LaurentBase D (v5LaurentEulerLinear b)) :
    ∃ Δ : v5WideSolutionAlgebra f ⊗[V5LaurentBase] D →+
        v5WideSolutionAlgebra f ⊗[V5LaurentBase] D,
      ∀ s d, Δ (s ⊗ₜ[V5LaurentBase] d) =
        (q • v5ActualSolutionEuler f A hA s) ⊗ₜ[V5LaurentBase] d +
          s ⊗ₜ[V5LaurentBase] dD d := by
  let ds := v5NatScaleDerivation132 q (v5ActualSolutionEulerDerivation131 f A hA)
  have hb : ∀ b : V5LaurentBase,
      ds (algebraMap V5LaurentBase (v5WideSolutionAlgebra f) b) ⊗ₜ[V5LaurentBase] (1 : D) =
        (1 : v5WideSolutionAlgebra f) ⊗ₜ[V5LaurentBase] dD (algebraMap V5LaurentBase D b) :=
    v5ActualSolutionBalanced132 f A hA dD q hD
  exact ⟨v5BalancedTensorEuler ds dD hb,
    fun s d => v5BalancedTensorEuler_tmul ds dD hb s d⟩

end StrictEUnit
#print axioms StrictEUnit.v5ActualSolutionBalanced132

#print axioms StrictEUnit.v5ActualSolutionTensorEuler132
