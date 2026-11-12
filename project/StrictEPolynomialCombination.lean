import Stage15StrictECoordinate
import Stage14StrictERingClosure
import AlgebraicScalarExponential

/-! Full strict-E closure for the polynomial combinations used in a cyclic
scalar reduction. No ordinary-point nonvanishing theorem is assumed. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators
namespace StrictEUnit

theorem strictEFunction_natPower {f : ℂ → ℂ} (hf : IsStrictEFunction f) (n : ℕ) :
    IsStrictEFunction (fun z => f z ^ n) := by
  induction n with
  | zero => simpa using algebraic_constant_isStrictEFunction (1 : AlgebraicComplex)
  | succ n ih => simpa only [pow_succ] using strictEFunction_mul ih hf

theorem strictEFunction_finsetSum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, IsStrictEFunction (f i)) :
    IsStrictEFunction (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using algebraic_constant_isStrictEFunction (0 : AlgebraicComplex)
  | @insert i s hi ih =>
    have hs := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using
      strictEFunction_add (hf i (Finset.mem_insert_self i s)) hs

theorem strictEFunction_polynomialEvaluation (p : Polynomial AlgebraicComplex) :
    IsStrictEFunction (fun z => p.eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [Polynomial.eval₂_add] using strictEFunction_add hp hq
  | monomial n c =>
    simpa only [Polynomial.eval₂_monomial] using
      strictEFunction_mul (algebraic_constant_isStrictEFunction c)
        (strictEFunction_natPower strictEFunction_coordinate n)

/-- The genuine cyclic scalar candidate retains all arithmetic bounds and a
nonzero algebraic differential equation, not only analyticity. -/
theorem strictEFunction_polynomialCombination {ι : Type*} [Fintype ι]
    (p : ι → Polynomial AlgebraicComplex) (f : ι → ℂ → ℂ)
    (hf : ∀ i, IsStrictEFunction (f i)) :
    IsStrictEFunction (fun z => ∑ i,
      (p i).eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z * f i z) := by
  apply strictEFunction_finsetSum
  intro i hi
  exact strictEFunction_mul (strictEFunction_polynomialEvaluation (p i)) (hf i)

end StrictEUnit
