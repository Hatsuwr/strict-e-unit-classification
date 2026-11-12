import Stage16LaurentMatrixClearing
import StrictEFunctionDefinitions

/-! Actual finite vectorization of a two-sided matrix system. This constructs
its coefficient matrix; it does not assert Beukers relation lifting. -/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- The coefficient matrix of X ↦ A X - X C in entry coordinates. -/
def twoSidedVectorMatrix {R n : Type*} [CommRing R] [DecidableEq n]
    (A C : Matrix n n R) : Matrix (n × n) (n × n) R :=
  fun ij kl => (if kl.2 = ij.2 then A ij.1 kl.1 else 0) -
    (if kl.1 = ij.1 then C kl.2 ij.2 else 0)

/-- Vectorization is an exact finite-sum identity, including empty matrices. -/
theorem twoSidedVectorMatrix_mulVec {R n : Type*} [CommRing R]
    [Fintype n] [DecidableEq n] (A C X : Matrix n n R) (i j : n) :
    ∑ kl : n × n, twoSidedVectorMatrix A C (i,j) kl * X kl.1 kl.2 =
      (∑ k, A i k * X k j) - ∑ k, X i k * C k j := by
  simp only [twoSidedVectorMatrix, sub_mul, Finset.sum_sub_distrib]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [mul_comm]

/-- Any ring evaluation commutes with the actual vectorized coefficients. -/
theorem twoSidedVectorMatrix_map {R S n : Type*} [CommRing R] [CommRing S]
    [DecidableEq n] (φ : R →+* S) (A C : Matrix n n R) (ij kl : n × n) :
    φ (twoSidedVectorMatrix A C ij kl) =
      twoSidedVectorMatrix (A.map φ) (C.map φ) ij kl := by
  simp [twoSidedVectorMatrix, apply_ite φ]

/-- An actual punctured two-sided Laurent system is a single first-order
system for the vector consisting of all entries. No transcendence theorem is
used in this algebraic conversion. -/
theorem laurentTwoSided_vector_system {n : Type*} [Fintype n] [DecidableEq n]
    (A C : Matrix n n (LaurentPolynomial ℂ)) (F : Matrix n n entireFunctionAlgebra)
    (hF : ∀ z : ℂˣ, ∀ i j, deriv (F i j).val (z : ℂ) =
      (∑ k, stage16_laurentEval z (A i k) * (F k j).val (z : ℂ)) -
        ∑ k, (F i k).val (z : ℂ) * stage16_laurentEval z (C k j)) :
    ∀ z : ℂˣ, ∀ ij : n × n, deriv (F ij.1 ij.2).val (z : ℂ) =
      ∑ kl : n × n, stage16_laurentEval z
        (twoSidedVectorMatrix A C ij kl) * (F kl.1 kl.2).val (z : ℂ) := by
  intro z ij
  simp_rw [twoSidedVectorMatrix_map]
  exact (hF z ij.1 ij.2).trans
    (twoSidedVectorMatrix_mulVec (A.map (stage16_laurentEval z))
      (C.map (stage16_laurentEval z)) (F.map (entireEvaluation (z : ℂ))) ij.1 ij.2).symm

end StrictEUnit
#print axioms StrictEUnit.twoSidedVectorMatrix
#print axioms StrictEUnit.twoSidedVectorMatrix_mulVec
#print axioms StrictEUnit.twoSidedVectorMatrix_map
#print axioms StrictEUnit.laurentTwoSided_vector_system
