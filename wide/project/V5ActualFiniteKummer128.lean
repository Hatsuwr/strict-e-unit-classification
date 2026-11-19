import V5CandidateKummer
import V5ActualCoverMark125

noncomputable section
set_option maxHeartbeats 180000
set_option maxRecDepth 1600
set_option synthInstance.maxHeartbeats 17000
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] [Algebra K ℂ] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K))

def v5_subalgebra_finite_marked_kummer128
    (T : Subalgebra (LaurentPolynomial K) (V5WideFieldCandidate A))
    (hF : @Module.Finite (LaurentPolynomial K) T inferInstance
      (Subalgebra.toCommRing T).toAddCommMonoid T.module') :=
  @v5_candidate_finite_marked_kummer K _ _ _ _ r A T
    (Subalgebra.toCommRing T) inferInstance T.algebra inferInstance hF
    T.val.toRingHom T.val.commutes

/-- Applies the checked analytic marked Kummer construction to the literal
fixed subring; only finiteness of that subring remains a premise. -/
def v5ActualFiniteKummer128
    (hF : @Module.Finite (LaurentPolynomial K) (v5ActualCover125 A) inferInstance
      (Subalgebra.toCommRing (v5ActualCover125 A)).toAddCommMonoid (v5ActualCover125 A).module') :=
  @v5_subalgebra_finite_marked_kummer128 K _ _ _ _ r A (v5ActualCover125 A) hF

end StrictEUnit
#print axioms StrictEUnit.v5_subalgebra_finite_marked_kummer128
#print axioms StrictEUnit.v5ActualFiniteKummer128
