import FormalMatrixLogRemoval

/-!
Algebraic inclusion criteria for the actual Laurent coefficient algebra. The
lemmas below construct range membership generator by generator; no realization
or convergence hypothesis for arbitrary formal series is introduced.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit

/-- A subalgebra containing the coordinate and its inverse contains every
finite Laurent polynomial under the fixed, coefficientwise embedding. -/
theorem stage19_laurentPolynomial_mem_of_coordinate
    {k : Type*} [Field k] (S : Subalgebra k (LaurentSeries k))
    (ht : laurentPolynomialToSeries (LaurentPolynomial.T 1) ∈ S)
    (hti : laurentPolynomialToSeries (LaurentPolynomial.T (-1)) ∈ S)
    (p : LaurentPolynomial k) : laurentPolynomialToSeries p ∈ S := by
  induction p using LaurentPolynomial.induction_on with
  | h_C a =>
    change laurentPolynomialToSeries (algebraMap k (LaurentPolynomial k) a) ∈ S
    rw [AlgHom.commutes]
    exact S.algebraMap_mem a
  | h_add hp hq =>
    rw [map_add]
    exact S.add_mem hp hq
  | h_C_mul_T n a ih =>
    rw [LaurentPolynomial.T_add, ← mul_assoc, map_mul]
    exact S.mul_mem ih ht
  | h_C_mul_T_Z n a ih =>
    rw [sub_eq_add_neg, LaurentPolynomial.T_add, ← mul_assoc, map_mul]
    exact S.mul_mem ih hti

/-- Inverse of an image of a genuine unit belongs to the same algebraic image. -/
theorem stage19_inverse_mem_range_of_isUnit
    {k R : Type*} [Field k] [CommRing R] [Algebra k R]
    (φ : R →ₐ[k] LaurentSeries k) (r : R) (hr : IsUnit r) :
    (φ r)⁻¹ ∈ φ.range := by
  obtain ⟨u, rfl⟩ := hr
  refine ⟨(↑u⁻¹ : R), ?_⟩
  apply eq_inv_of_mul_eq_one_right
  change φ (↑u : R) * φ (↑u⁻¹ : R) = 1
  rw [← map_mul, Units.mul_inv, map_one]

/-- A range containing the actual entries, finite Laurent polynomials and
inverse determinant contains the actual formal matrix coefficient algebra. -/
theorem stage19_formalMatrixCoefficientAlgebra_le
    {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n]
    (F : Matrix n n (LaurentSeries k)) (S : Subalgebra k (LaurentSeries k))
    (ht : laurentPolynomialToSeries (LaurentPolynomial.T 1) ∈ S)
    (hti : laurentPolynomialToSeries (LaurentPolynomial.T (-1)) ∈ S)
    (hdet : F.det⁻¹ ∈ S) (hF : ∀ i j, F i j ∈ S) :
    formalMatrixCoefficientAlgebra F ≤ S := by
  apply Algebra.adjoin_le
  rintro x (⟨p, rfl⟩ | (rfl | ⟨⟨i, j⟩, rfl⟩))
  · exact stage19_laurentPolynomial_mem_of_coordinate S ht hti p
  · exact hdet
  · exact hF i j

end StrictEUnit
