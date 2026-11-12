import ActualFrameFiberExponentialDescent
import Stage24CommonFrameValueCoverage
import Stage23ActualFrameFiber
import Stage25InverseValuesDescent
import AlgebraicScalarExponential

/-! Conditional end-to-end classification from two explicitly unproved inputs:
common arithmetic-frame availability and exact Beukers relation lifting.
Neither input is declared as an axiom, and neither is proved by this file.
All intermediate formal/analytic/fiber/unit interfaces are derived. -/
noncomputable section
open scoped TensorProduct
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] formalAmbientBaseAlgebra
attribute [local instance 2000] formalAmbientBaseTower
attribute [local instance 10] laurentLogPointAlgebra laurentLogPointTower
attribute [local instance 2000] Algebra.toModule
attribute [local instance 2000] stage22CanonicalScalarCommRing stage22CanonicalScalarCommSemiring
attribute [local instance 2000] stage22CanonicalScalarSemiring stage22CanonicalScalarAddCommMonoid
attribute [local instance 2000] stage22CanonicalScalarMonoid stage22CanonicalComplexCommRing
attribute [local instance 2000] stage22CanonicalComplexSemiring stage22CanonicalCandidateCommRing
attribute [local instance 2000] stage22CanonicalCandidateSemiring stage22CanonicalCandidateAddCommMonoid
attribute [local instance 2000] stage22CanonicalCandidateMonoid
attribute [local instance 2000] stage19CoefficientMonoid
local notation "k₀" => IntermediateField.toSubfield (algebraicClosure ℚ ℂ)

/-- The forward numerical classification, conditional precisely on the two
named arithmetic input propositions. Separate reciprocal representatives are
carried through the same exact numerical fiber before regular-unit lifting. -/
theorem strictEValueUnit_exponential_form_of_arithmetic_inputs
    (hAndre : StrictECommonArithmeticFrameAvailability)
    (hBeukers : StrictELaurentRelationLifting)
    (u : ℂ) (hu : IsStrictEValueUnit u) : HasExponentialForm k₀ u := by
  letI : IsAlgClosed k₀ := stage17_algebraicTaylorField_isAlgClosed
  obtain ⟨d, B, M, F, hstrict, hrat, hF, h1, hfu, hfui⟩ :=
    strictEValueUnit_common_frame_values hAndre u hu
  obtain ⟨N, hN, Z, hZ, hpoint, hunit, hODE⟩ :=
    stage17_algebraicFrame_exists_formalFundamental B M F hrat hF h1
  let G := stage19_formalMatrix k₀ N (stage19_ramifiedBoundedMatrix k₀ N hN F hstrict)
  let Y := G.map RatFunc.C * (Z : Matrix (Fin d) (Fin d) (LaurentLogBase k₀)).map
    (algebraMap (LaurentLogBase k₀) (RatFunc (LaurentSeries k₀)))
  have hY : Y = stage17_formalFundamental k₀ N hN F Z := by
    dsimp only [Y, G]
    rw [stage19_ramifiedFormalMatrix_compatibility]
    rfl
  have hdet : Y.det ≠ 0 := by
    rw [hY]
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hunit)
  have hy : ∀ i j, formalAmbientDerivation N hN (Y i j) =
      ∑ l, formalBaseEmbedding ((B.map (stage17_laurentBasePullback k₀ N)) i l) * Y l j := by
    rw [← hY] at hODE
    intro i j
    exact congrArg (fun T : Matrix (Fin d) (Fin d) (RatFunc (LaurentSeries k₀)) => T i j) hODE
  exact actualFrameFiber_inverseValuesExponentialForm hBeukers N hN B M F hstrict hF h1 Z
    hdet hy u hu.1 hfu hfui



/-- Complete iff for the original numerical strict-E predicate, CONDITIONAL
on the two named unproved arithmetic inputs. The reverse implication is the
unconditional, previously constructed strict-E exponential inclusion. -/
theorem strictEValueUnit_iff_algebraic_scalar_exp_of_arithmetic_inputs
    (hAndre : StrictECommonArithmeticFrameAvailability)
    (hBeukers : StrictELaurentRelationLifting) (u : ℂ) :
    IsStrictEValueUnit u ↔
      ∃ α β : ℂ, IsAlgebraic ℚ α ∧ α ≠ 0 ∧ IsAlgebraic ℚ β ∧
        u = α * Complex.exp β := by
  constructor
  · intro hu
    obtain ⟨α, hα, hα0, β, hβ, he⟩ :=
      strictEValueUnit_exponential_form_of_arithmetic_inputs hAndre hBeukers u hu
    exact ⟨α, β, mem_algebraicClosure_iff.mp hα, hα0, mem_algebraicClosure_iff.mp hβ, he⟩
  · exact algebraic_exponential_reverse_inclusion

end StrictEUnit
#print axioms StrictEUnit.strictEValueUnit_exponential_form_of_arithmetic_inputs
#print axioms StrictEUnit.strictEValueUnit_iff_algebraic_scalar_exp_of_arithmetic_inputs
