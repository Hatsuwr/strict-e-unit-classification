import V5GenericOwnFixed123
import V5ComponentCoverFromOwnChart

noncomputable section
open scoped TensorProduct
set_option maxHeartbeats 190000
set_option maxRecDepth 1600
set_option synthInstance.maxHeartbeats 18000
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K))

/-- Literal restricted own fixed algebra of the actual centered candidate. -/
def v5ActualCover125 : Subalgebra (LaurentPolynomial K) (V5WideFieldCandidate A) :=
  v5CanonicalComponentCover (v5WideOwnCoaction A) (v5GenericOwnIdentity123 A)

def v5ActualCoverInclusion125 : v5ActualCover125 A →+* V5WideFieldCandidate A :=
  (v5ActualCover125 A).val.toRingHom

theorem v5ActualCoverInclusion125_injective :
    Function.Injective (v5ActualCoverInclusion125 A) := Subtype.val_injective

theorem v5ActualCoverInclusion125_base (p : LaurentPolynomial K) :
    v5ActualCoverInclusion125 A (algebraMap (LaurentPolynomial K) (v5ActualCover125 A) p) =
      algebraMap (LaurentPolynomial K) (V5WideFieldCandidate A) p :=
  (v5ActualCover125 A).val.commutes p

def v5ActualCoverPoint125 : v5ActualCover125 A →+* K :=
  (v5WideFieldCandidatePoint A).toRingHom.comp (v5ActualCoverInclusion125 A)

theorem v5ActualCoverPoint125_base (p : LaurentPolynomial K) :
    v5ActualCoverPoint125 A (algebraMap (LaurentPolynomial K) (v5ActualCover125 A) p) =
      LaurentPolynomial.eval₂ (RingHom.id K) (1 : Kˣ) p := by
  change v5WideFieldCandidatePoint A (v5ActualCoverInclusion125 A
    (algebraMap (LaurentPolynomial K) (v5ActualCover125 A) p)) = _
  rw [v5ActualCoverInclusion125_base, v5WideFieldCandidatePoint_base]

end StrictEUnit
#print axioms StrictEUnit.v5ActualCover125
#print axioms StrictEUnit.v5ActualCoverInclusion125_injective
#print axioms StrictEUnit.v5ActualCoverInclusion125_base
#print axioms StrictEUnit.v5ActualCoverPoint125_base
