import V5ActualKummerEuler129
import V5ActualCoverProperties131
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 600000
set_option maxRecDepth 1800
set_option synthInstance.maxHeartbeats 15000
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {r : ℕ}
  (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K))
/-- Recover Euler compatibility for the exact Kummer map already chosen
in the reciprocal lift, using only its full Laurent power-map identity. -/
def v5ActualSameKummerEuler136
    (q : ℕ) (α : v5ActualCover125 A →ₐ[K] LaurentPolynomial K)
    (hbase : α.toRingHom.comp (algebraMap (LaurentPolynomial K) (v5ActualCover125 A)) =
      v5LaurentPower q) := by
  letI : @Algebra.FormallyUnramified (LaurentPolynomial K) (v5ActualCover125 A) inferInstance
      (Subalgebra.toCommRing (v5ActualCover125 A)) (v5ActualCover125 A).algebra :=
    v5ActualCoverFormallyUnramified131 A
  exact v5_subalgebra_kummer_euler127 (v5ActualCover125 A)
    (v5ActualCoverDerivation126 A) (v5ActualCoverDerivation126_base A) α q
    ((RingHom.congr_fun hbase (LaurentPolynomial.T 1)).trans (v5_laurentPower_coordinate129 q))
end StrictEUnit
#print axioms StrictEUnit.v5ActualSameKummerEuler136
