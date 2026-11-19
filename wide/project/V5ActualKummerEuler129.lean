import V5ActualFiniteKummer128
import V5CoverEulerKummer127

noncomputable section
set_option maxHeartbeats 180000
set_option maxRecDepth 1600
set_option synthInstance.maxHeartbeats 17000
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing
namespace StrictEUnit

theorem v5_laurentPower_coordinate129 {K : Type*} [Field K] (q : ℕ) :
    (v5LaurentPower q) (LaurentPolynomial.T 1 : LaurentPolynomial K) =
      (LaurentPolynomial.T 1)^q := by
  unfold v5LaurentPower
  rw [LaurentPolynomial.eval₂_T, zpow_one]
  simp only [LaurentPolynomial.T_pow, mul_one]

theorem v5_subalgebra_refine_marked_kummer129
    {K R C : Type*} [Field K] [CommRing R] [Algebra K R]
    [Algebra (LaurentPolynomial K) R] [IsScalarTower K (LaurentPolynomial K) R]
    (T : Subalgebra (LaurentPolynomial K) R) [Algebra.FormallyUnramified (LaurentPolynomial K) T]
    (d : Derivation K T T)
    (hd : ∀ p, d (algebraMap (LaurentPolynomial K) T p) =
      algebraMap (LaurentPolynomial K) T (v5LaurentBaseDerivation p))
    (mark : T → C) (evaluate : LaurentPolynomial K → C)
    (hK : ∃ (q : ℕ) (_ : 0 < q) (α : T →ₐ[K] LaurentPolynomial K),
      α.toRingHom.comp (algebraMap (LaurentPolynomial K) T) = v5LaurentPower q ∧
      ∀ x, evaluate (α x) = mark x) :
    ∃ (q : ℕ) (_ : 0 < q) (α : T →ₐ[K] LaurentPolynomial K),
      α.toRingHom.comp (algebraMap (LaurentPolynomial K) T) = v5LaurentPower q ∧
      (∀ x, evaluate (α x) = mark x) ∧
      (∀ x, v5LaurentEulerDerivation127 (α x) =
        (q : LaurentPolynomial K) * α (v5SubalgebraEuler127 T d x)) := by
  obtain ⟨q, hq, α, hB, hm⟩ := hK
  refine ⟨q, hq, α, hB, hm, ?_⟩
  apply v5_subalgebra_kummer_euler127 T d hd α q
  exact (RingHom.congr_fun hB (LaurentPolynomial.T 1)).trans
    (v5_laurentPower_coordinate129 q)

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] [Algebra K ℂ] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K))

def v5ActualFiniteKummerEuler129
    (hF : @Module.Finite (LaurentPolynomial K) (v5ActualCover125 A) inferInstance
      (Subalgebra.toCommRing (v5ActualCover125 A)).toAddCommMonoid (v5ActualCover125 A).module')
    (hU : @Algebra.FormallyUnramified (LaurentPolynomial K) (v5ActualCover125 A) inferInstance
      (Subalgebra.toCommRing (v5ActualCover125 A)) (v5ActualCover125 A).algebra) :=
  letI := hU
  v5_subalgebra_refine_marked_kummer129 (v5ActualCover125 A)
    (v5ActualCoverDerivation126 A) (v5ActualCoverDerivation126_base A) _ _
    (v5ActualFiniteKummer128 A hF)

end StrictEUnit
#print axioms StrictEUnit.v5_laurentPower_coordinate129
#print axioms StrictEUnit.v5_subalgebra_refine_marked_kummer129
#print axioms StrictEUnit.v5ActualFiniteKummerEuler129
