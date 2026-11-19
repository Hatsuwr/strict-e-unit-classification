import V5GenericPVTrivialization
import V5WidePointedDifferential
import V5WidePointedFieldCandidate
import CandidateCoaction
import CandidateDifferentialCoaction
import CandidateCounit

noncomputable section
open scoped TensorProduct
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule
attribute [-instance] HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
namespace StrictEUnit
variable {k : Type*} [Field k] [CharZero k] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial k))

theorem v5WideOwnFundamental_ode (i j : Fin r) :
    stage14_laurentAlgebraDerivation (v5WidePointedLaurentFundamental A i j) =
      ∑ l, algebraMap (LaurentPolynomial k) (LaurentSeries k) (A i l) *
        v5WidePointedLaurentFundamental A l j := by
  simpa only [Matrix.mul_apply, Matrix.map_apply] using
    v5WidePointedLaurentFundamental_equation A i j

theorem v5WideOwnFundamental_det_ne_zero :
    (v5WidePointedLaurentFundamental A).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp (v5WidePointedLaurentFundamental_isUnit A)).ne_zero

theorem v5WideOwnBase_differential (b : LaurentPolynomial k) :
    stage14_laurentAlgebraDerivation (algebraMap (LaurentPolynomial k) (LaurentSeries k) b) =
      algebraMap (LaurentPolynomial k) (LaurentSeries k) (v5LaurentBaseDerivation b) :=
  v5WidePointedLaurentBase_differential b

def v5WideOwnDerivation : Derivation k (V5WideFieldCandidate A) (V5WideFieldCandidate A) :=
  candidateKDerivation v5LaurentBaseDerivation stage14_laurentAlgebraDerivation
    (v5WidePointedLaurentFundamental A) A v5WideOwnBase_differential (v5WideOwnFundamental_ode A)

theorem v5WideOwnDerivation_base (b : LaurentPolynomial k) :
    v5WideOwnDerivation A (algebraMap (LaurentPolynomial k) (V5WideFieldCandidate A) b) =
      algebraMap (LaurentPolynomial k) (V5WideFieldCandidate A) (v5LaurentBaseDerivation b) :=
  candidateKDerivation_base v5LaurentBaseDerivation stage14_laurentAlgebraDerivation
    (v5WidePointedLaurentFundamental A) A v5WideOwnBase_differential (v5WideOwnFundamental_ode A) b

theorem v5WideOwn_constants (x : LaurentSeries k)
    (hx : stage14_laurentAlgebraDerivation x = 0) :
    ∃ c : k, algebraMap k (LaurentSeries k) c = x := by
  obtain ⟨c, hc⟩ := (laurentOrdinaryDerivation_eq_zero_iff_exists_constant x).mp hx
  exact ⟨c, hc.symm⟩

/-- The own-PV square comparison for the actual centered fundamental matrix.
No flatness, differential-simplicity or constant-field assumptions remain. -/
theorem v5WideOwnMultiplication_bijective :
    Function.Bijective (pvConstantMultiplication v5LaurentBaseDerivation
      (v5WideOwnDerivation A) (v5WideOwnDerivation_base A)) :=
  v5_candidateConstantMultiplication_bijective_of_simple_base
    v5LaurentBaseDerivation stage14_laurentAlgebraDerivation
    (v5WidePointedLaurentFundamental A) A (v5WideOwnFundamental_det_ne_zero A)
    v5WideOwnBase_differential (v5WideOwnFundamental_ode A)
    v5LaurentBase_stable_ideal_eq_top v5WideOwn_constants

def v5WideOwnMultiplicationEquiv :=
  AlgEquiv.ofBijective (pvConstantMultiplication v5LaurentBaseDerivation
    (v5WideOwnDerivation A) (v5WideOwnDerivation_base A))
    (v5WideOwnMultiplication_bijective A)

def v5WideOwnCoaction :=
  inverseMultiplicationCoaction (v5WideOwnMultiplicationEquiv A)

theorem v5WideOwnCoaction_canonical_bijective :
    Function.Bijective (relativeCandidateCanonical (v5WideOwnCoaction A)) :=
  relativeCandidateCanonical_bijective _

theorem v5WideOwnCoaction_differential (x : V5WideFieldCandidate A) :
    tensorDerivation (v5WideOwnDerivation A) (v5WideOwnCoaction A x) =
      v5WideOwnCoaction A (v5WideOwnDerivation A x) :=
  inverseMultiplicationCoaction_differential _ _ _
    (v5WideOwnMultiplication_bijective A) x

theorem v5WideOwnDerivation_constants (x : V5WideFieldCandidate A)
    (hx : v5WideOwnDerivation A x = 0) :
    ∃ c : k, algebraMap k (V5WideFieldCandidate A) c = x :=
  candidateKDerivation_constants v5LaurentBaseDerivation stage14_laurentAlgebraDerivation
    (v5WidePointedLaurentFundamental A) A v5WideOwnBase_differential
    (v5WideOwnFundamental_ode A) v5WideOwn_constants x hx

/-- The coaction retains the original element under the actual diagonal counit.
This is not yet the coassociativity or mixed action theorem. -/
theorem v5WideOwnCoaction_counit (x : V5WideFieldCandidate A) :
    candidateCounitEval v5LaurentBaseDerivation (v5WideOwnDerivation A)
      (v5WideOwnDerivation_base A) (v5WideOwnDerivation_constants A)
      (v5WideOwnCoaction A x) = x :=
  candidateCounit_identity _ _ _ _ (v5WideOwnMultiplication_bijective A) x

end StrictEUnit
#print axioms StrictEUnit.v5WideOwnMultiplication_bijective
#print axioms StrictEUnit.v5WideOwnCoaction_canonical_bijective
#print axioms StrictEUnit.v5WideOwnCoaction_differential
#print axioms StrictEUnit.v5WideOwnDerivation_constants
#print axioms StrictEUnit.v5WideOwnCoaction_counit
