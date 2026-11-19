import V5ActualCoverDifferential126

noncomputable section
set_option maxHeartbeats 180000
set_option synthInstance.maxHeartbeats 15000
set_option maxRecDepth 1600
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing
namespace StrictEUnit

def v5EulerOfLaurent127 {K T : Type*} [Field K] [CommRing T]
    [Algebra K T] [Algebra (LaurentPolynomial K) T] (d : Derivation K T T) :
    Derivation K T T :=
  algebraMap (LaurentPolynomial K) T (LaurentPolynomial.T 1) • d

theorem v5_laurent_euler_ordinary127 {K : Type*} [Field K] (p : LaurentPolynomial K) :
    LaurentPolynomial.T 1 * v5LaurentBaseDerivation p = v5LaurentEulerLinear p := by
  change LaurentPolynomial.T 1 * (LaurentPolynomial.T (-1) * v5LaurentEulerLinear p) = _
  rw [← mul_assoc, ← LaurentPolynomial.T_add]
  norm_num

theorem v5_eulerOfLaurent_base127 {K T : Type*} [Field K] [CommRing T]
    [Algebra K T] [Algebra (LaurentPolynomial K) T]
    (d : Derivation K T T)
    (hd : ∀ p, d (algebraMap (LaurentPolynomial K) T p) =
      algebraMap (LaurentPolynomial K) T (v5LaurentBaseDerivation p))
    (p : LaurentPolynomial K) :
    v5EulerOfLaurent127 d (algebraMap (LaurentPolynomial K) T p) =
      algebraMap (LaurentPolynomial K) T (v5LaurentEulerLinear p) := by
  change algebraMap (LaurentPolynomial K) T (LaurentPolynomial.T 1) *
    d (algebraMap (LaurentPolynomial K) T p) = _
  rw [hd, ← map_mul, v5_laurent_euler_ordinary127]

def v5SubalgebraEuler127 {K R : Type*} [Field K] [CommRing R]
    [Algebra K R] [Algebra (LaurentPolynomial K) R] [IsScalarTower K (LaurentPolynomial K) R]
    (T : Subalgebra (LaurentPolynomial K) R) (d : Derivation K T T) :
    Derivation K T T :=
  v5EulerOfLaurent127 d

theorem v5_subalgebraEuler_base127 {K R : Type*} [Field K] [CommRing R]
    [Algebra K R] [Algebra (LaurentPolynomial K) R] [IsScalarTower K (LaurentPolynomial K) R]
    (T : Subalgebra (LaurentPolynomial K) R) (d : Derivation K T T)
    (hd : ∀ p, d (algebraMap (LaurentPolynomial K) T p) =
      algebraMap (LaurentPolynomial K) T (v5LaurentBaseDerivation p))
    (p : LaurentPolynomial K) :
    v5SubalgebraEuler127 T d (algebraMap (LaurentPolynomial K) T p) =
      algebraMap (LaurentPolynomial K) T (v5LaurentEulerLinear p) :=
  v5_eulerOfLaurent_base127 d hd p

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K))

def v5ActualCoverEuler127 :=
  v5SubalgebraEuler127 (v5ActualCover125 A) (v5ActualCoverDerivation126 A)

theorem v5ActualCoverEuler127_base (p : LaurentPolynomial K) :
    v5ActualCoverEuler127 A (algebraMap (LaurentPolynomial K) (v5ActualCover125 A) p) =
      algebraMap (LaurentPolynomial K) (v5ActualCover125 A) (v5LaurentEulerLinear p) :=
  v5_subalgebraEuler_base127 (v5ActualCover125 A) (v5ActualCoverDerivation126 A) (v5ActualCoverDerivation126_base A) p

end StrictEUnit
#print axioms StrictEUnit.v5_laurent_euler_ordinary127
#print axioms StrictEUnit.v5_eulerOfLaurent_base127
#print axioms StrictEUnit.v5ActualCoverEuler127
#print axioms StrictEUnit.v5ActualCoverEuler127_base
