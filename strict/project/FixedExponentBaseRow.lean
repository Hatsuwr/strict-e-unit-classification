import FiniteLogBaseIdentification
noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K I R : Type*} [Field K] [CharZero K] [Fintype I] [DecidableEq I]
  [CommRing R]

theorem fixedExponentBaseUnit_entry (m : ℤ) (J : Matrix I I K)
    (hJ : IsNilpotent J) (i j : I) :
    (fixedExponentBaseUnit m J hJ).val i j =
      Polynomial.C (LaurentPolynomial.T m) *
      Polynomial.map (algebraMap K (LaurentPolynomial K))
        (finiteLogMatrixExponential J i j) := by
  change (Matrix.diagonal (fun _ : I => (Polynomial.C (LaurentPolynomial.T m) : LaurentLogBase K)) *
    (ramifiedLogUnit J hJ).val) i j = _
  rw [← finiteLogMatrixExponential_map_base J hJ]
  simp [Matrix.diagonal_mul]

/-- Exact external-power factorization under any ring interpretation of the base.
The interpretation can later be specialized to the formal ramified embedding. -/
theorem fixedExponentBaseUnit_row (f : LaurentLogBase K →+* R)
    (F : I → R) (m : ℤ) (J : Matrix I I K) (hJ : IsNilpotent J) (j : I) :
    (∑ i, F i * f ((fixedExponentBaseUnit m J hJ).val i j)) =
      f ((Polynomial.C (LaurentPolynomial.T m) : LaurentLogBase K)) *
      ∑ i, F i * f (Polynomial.map (algebraMap K (LaurentPolynomial K))
        (finiteLogMatrixExponential J i j)) := by
  simp_rw [fixedExponentBaseUnit_entry, map_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
end StrictEUnit
end
