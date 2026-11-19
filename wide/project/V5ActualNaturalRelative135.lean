import V5NaturalHopfRelative135
import V5ActualCoverType126
import V5WideOwnPVAction
import V5WideOwnReduced
noncomputable section
open scoped TensorProduct
set_option maxHeartbeats 600000
set_option maxRecDepth 1600
set_option synthInstance.maxHeartbeats 15000
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {r : ℕ}
  (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K))
def v5ActualNaturalRelative135 := by
  letI := v5WideOwnHopfAlgebra A
  letI : Algebra.FiniteType K (V5WideOwnConstants A) := v5WideOwnConstants_finiteType A
  letI := v5WideOwnConstants_isReduced A
  letI := v5WideOwnCandidate_faithfullyFlat A
  let spec := (Classical.choose_spec (v5GenericOwnUniqueIdentity123 A)).1
  let uniq := (Classical.choose_spec (v5GenericOwnUniqueIdentity123 A)).2
  exact v5NaturalHopfRelative135
    (k := K) (B := LaurentPolynomial K)
    (R := V5WideFieldCandidate A) (H := V5WideOwnConstants A)
    (v5WideOwnMultiplicationEquiv A) (v5WideOwnCoaction A)
    (by intro r s; exact v5_ownChart_tmul_smul (v5WideOwnMultiplicationEquiv A) r s)
    (v5WideOwnCoaction_coassoc A)
    (v5WideOwnAntipode A) rfl (v5GenericOwnIdentity123 A) spec.1 spec.2
    (fun P hP hPε => uniq P ⟨hP, hPε⟩)
end StrictEUnit
#print axioms StrictEUnit.v5ActualNaturalRelative135
