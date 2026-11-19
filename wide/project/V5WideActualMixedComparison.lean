import V5MixedSystemComparison
import V5WideSolutionBaseDifferential
import V5WidePointedFieldCandidate
import V5GenericPVTrivialization
import V5WidePointedDifferential

open scoped TensorProduct
open TensorProduct
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 1800
set_option synthInstance.maxHeartbeats 120000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule
attribute [-instance] HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
namespace StrictEUnit
variable {r : ℕ}
    (f : Fin r → entireFunctionAlgebra)
    (A : Matrix (Fin r) (Fin r) V5LaurentBase)
    (hA : ∀ z : ℂˣ, ∀ i, deriv (f i).val (z : ℂ) =
      ∑ j, arithmeticLaurentEvaluation z (A i j) * (f j).val (z : ℂ))

theorem v5WideFieldFundamental_ode (i j : Fin r) :
    laurentOrdinaryDerivation (v5WidePointedLaurentFundamental A i j) =
      ∑ l, algebraMap V5LaurentBase (LaurentSeries AlgebraicComplex) (A i l) *
        v5WidePointedLaurentFundamental A l j := by
  simpa only [Matrix.mul_apply, Matrix.map_apply] using
    v5WidePointedLaurentFundamental_equation A i j

theorem v5WideFieldFundamental_det_ne_zero :
    (v5WidePointedLaurentFundamental A).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp (v5WidePointedLaurentFundamental_isUnit A)).ne_zero

theorem v5WideFieldBase_differential (b : V5LaurentBase) :
    laurentOrdinaryDerivation (algebraMap V5LaurentBase (LaurentSeries AlgebraicComplex) b) =
      algebraMap V5LaurentBase (LaurentSeries AlgebraicComplex) (v5LaurentBaseDerivation b) :=
  v5WidePointedLaurentBase_differential b

def v5WideFieldCandidateDerivation :
    Derivation AlgebraicComplex (V5WideFieldCandidate A) (V5WideFieldCandidate A) :=
  candidateKDerivation v5LaurentBaseDerivation stage14_laurentAlgebraDerivation
    (v5WidePointedLaurentFundamental A) A v5WideFieldBase_differential (v5WideFieldFundamental_ode A)

theorem v5WideFieldCandidate_base (b : V5LaurentBase) :
    v5WideFieldCandidateDerivation A (algebraMap V5LaurentBase (V5WideFieldCandidate A) b) =
      algebraMap V5LaurentBase (V5WideFieldCandidate A) (v5LaurentBaseDerivation b) :=
  candidateKDerivation_base v5LaurentBaseDerivation stage14_laurentAlgebraDerivation
    (v5WidePointedLaurentFundamental A) A v5WideFieldBase_differential (v5WideFieldFundamental_ode A) b

def v5WideActualMixedComparison := by
  letI := v5WideSolution_faithfullyFlat f A hA v5LaurentBaseDerivation
    (v5WideSolution_base_compatible f A hA) v5LaurentBase_stable_ideal_eq_top
  refine v5MixedSystemComparisonEquiv (k := AlgebraicComplex) (B := V5LaurentBase)
    (E := LaurentSeries AlgebraicComplex) v5LaurentBaseDerivation
    (v5WideFieldCandidateDerivation A) (v5WideSolutionDerivation f A hA) (v5WideFieldCandidate_base A)
    (v5WideSolution_base_compatible f A hA)
    stage14_laurentAlgebraDerivation (V5WideFieldCandidate A).val Subtype.val_injective
    (fun _ => rfl) (fun x hx => ?_) A
    (candidateMatrixUnit (v5WidePointedLaurentFundamental A) (v5WideFieldFundamental_det_ne_zero A))
    (v5WideSolutionEntry f) ?_ ?_ (v5WideSolutionLaurent_generates f)
  · obtain ⟨c, hc⟩ := (laurentOrdinaryDerivation_eq_zero_iff_exists_constant x).mp hx
    exact ⟨c, hc.symm⟩
  · exact candidateKDerivation_ode v5LaurentBaseDerivation stage14_laurentAlgebraDerivation
      (v5WidePointedLaurentFundamental A) A _ v5WideFieldBase_differential (v5WideFieldFundamental_ode A)
  · intro i
    simpa only [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply] using
      v5WideSolutionDerivation_entry f A hA i

end StrictEUnit
#print axioms StrictEUnit.v5WideActualMixedComparison
