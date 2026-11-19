import V5ActualCoverEuler127
import V5LaurentEuler

noncomputable section
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [local instance 2000] Algebra.toModule
namespace StrictEUnit

def v5LaurentEulerDerivation127 {K : Type*} [Field K] :
    Derivation K (LaurentPolynomial K) (LaurentPolynomial K) :=
  v5EulerOfLaurent127 v5LaurentBaseDerivation

@[simp] theorem v5LaurentEulerDerivation127_apply {K : Type*} [Field K]
    (p : LaurentPolynomial K) :
    v5LaurentEulerDerivation127 p = v5LaurentEulerLinear p :=
  v5_laurent_euler_ordinary127 p

@[simp] theorem v5LaurentEulerDerivation127_coordinate {K : Type*} [Field K] :
    v5LaurentEulerDerivation127 (LaurentPolynomial.T 1 : LaurentPolynomial K) =
      LaurentPolynomial.T 1 := by
  rw [v5LaurentEulerDerivation127_apply]
  change v5LaurentEulerLinear (Finsupp.single 1 1) = _
  rw [v5LaurentEulerLinear_single]
  simp

theorem v5_subalgebra_kummer_euler127 {K R : Type*} [Field K] [CommRing R]
    [Algebra K R] [Algebra (LaurentPolynomial K) R] [IsScalarTower K (LaurentPolynomial K) R]
    (T : Subalgebra (LaurentPolynomial K) R) [Algebra.FormallyUnramified (LaurentPolynomial K) T]
    (d : Derivation K T T)
    (hd : ∀ p, d (algebraMap (LaurentPolynomial K) T p) =
      algebraMap (LaurentPolynomial K) T (v5LaurentBaseDerivation p))
    (f : T →ₐ[K] LaurentPolynomial K) (q : ℕ)
    (hcoord : f (algebraMap (LaurentPolynomial K) T (LaurentPolynomial.T 1)) =
      (LaurentPolynomial.T 1)^q) :
    ∀ x : T, v5LaurentEulerDerivation127 (f x) =
      (q : LaurentPolynomial K) * f (v5SubalgebraEuler127 T d x) := by
  apply v5_unramified_laurent_kummer_differential_map f v5LaurentEulerDerivation127
    (v5SubalgebraEuler127 T d) v5LaurentEulerDerivation127
  · intro p
    rw [v5LaurentEulerDerivation127_apply]
    exact v5_subalgebraEuler_base127 T d hd p
  · exact v5LaurentEulerDerivation127_coordinate
  · exact v5LaurentEulerDerivation127_coordinate
  · exact hcoord

end StrictEUnit
#print axioms StrictEUnit.v5LaurentEulerDerivation127
#print axioms StrictEUnit.v5LaurentEulerDerivation127_apply
#print axioms StrictEUnit.v5LaurentEulerDerivation127_coordinate
#print axioms StrictEUnit.v5_subalgebra_kummer_euler127
