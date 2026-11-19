import V5ActualKummerExponential140
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1800
set_option synthInstance.maxHeartbeats 20000
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
attribute [local instance 5000] Subalgebra.algebra Subalgebra.algebra' Subalgebra.toCommRing
namespace StrictEUnit
local instance : IsAlgClosed AlgebraicComplex := IsAlgClosure.isAlgClosed ℚ
/-- The actual reciprocal value endpoint for a broad E-function Laurent
system. The cover map, degree, correcting unit, first-order equation, and
analytic realization are all constructed by the checked chain. -/
theorem v5ActualReciprocalExponential140
    {r : ℕ} (f : Fin r → entireFunctionAlgebra)
    (A : Matrix (Fin r) (Fin r) V5LaurentBase)
    (hf : ∀ i, V5IsBroadEFunction (f i).val)
    (hA : ∀ z : ℂˣ, ∀ i, deriv (f i).val (z : ℂ) =
      ∑ j, arithmeticLaurentEvaluation z (A i j) * (f j).val (z : ℂ))
    (i j : Fin r) (hij : (f i).val 1 * (f j).val 1 = 1) :
    ∃ a b : AlgebraicComplex, a ≠ 0 ∧ (f i).val 1 = (a : ℂ) * Complex.exp (b : ℂ) := by
  letI : CommRing (v5ActualCover125 A) := (v5ActualCover125 A).toCommRing
  letI : Algebra AlgebraicComplex (v5ActualCover125 A) :=
    Subalgebra.algebra' (R' := AlgebraicComplex) (v5ActualCover125 A)
  obtain ⟨q,hq,α,hbase,hm⟩ := v5ActualAlgebraicMarkedKummer135 A
  exact v5ActualKummerExponential140 f A hf hA q hq α hbase hm i j hij
end StrictEUnit
#print axioms StrictEUnit.v5ActualReciprocalExponential140
