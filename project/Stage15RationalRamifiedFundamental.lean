import Stage15RationalMatrixConjugation

/-! An actual normalized ramified fundamental unit for an arbitrary constant
matrix over an algebraically closed characteristic-zero field with rational
minimal-polynomial roots. No eigenbasis or Jordan decomposition is an input. -/
noncomputable section
namespace StrictEUnit
variable {k n : Type*} [Field k] [CharZero k] [Fintype n] [DecidableEq n]

/-- Embed a constant matrix unit into the manuscript's Laurent-log base ring. -/
def stage15_constant_matrix_unit (P : (Matrix n n k)ˣ) :
    (Matrix n n (LaurentLogBase k))ˣ :=
  Units.map (algebraMap k (LaurentLogBase k)).mapMatrix.toMonoidHom P

omit [CharZero k] in
/-- Conjugating by an actual constant unit preserves the differential equation,
while conjugating its coefficient matrix by the same constant unit. -/
theorem stage15_constant_conjugation_derivative
    (d : Derivation k (LaurentLogBase k) (LaurentLogBase k))
    (P : (Matrix n n k)ˣ) (A : Matrix n n k)
    (Z : (Matrix n n (LaurentLogBase k))ˣ)
    (hZ : matrixDerivative d (Z : Matrix n n (LaurentLogBase k)) =
      ramifiedConstantMatrix A * (Z : Matrix n n (LaurentLogBase k))) :
    matrixDerivative d
      (↑(stage15_constant_matrix_unit P * Z * (stage15_constant_matrix_unit P)⁻¹) :
        Matrix n n (LaurentLogBase k)) =
      ramifiedConstantMatrix ((P : Matrix n n k) * A * (↑P⁻¹ : Matrix n n k)) *
      (↑(stage15_constant_matrix_unit P * Z * (stage15_constant_matrix_unit P)⁻¹) :
        Matrix n n (LaurentLogBase k)) := by
  let C : Matrix n n k →+* Matrix n n (LaurentLogBase k) :=
    (algebraMap k (LaurentLogBase k)).mapMatrix
  have hC : C (↑P⁻¹ : Matrix n n k) * C (P : Matrix n n k) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  change matrixDerivative d (C (P : Matrix n n k) * (Z : Matrix n n (LaurentLogBase k)) *
      C (↑P⁻¹ : Matrix n n k)) =
    C ((P : Matrix n n k) * A * (↑P⁻¹ : Matrix n n k)) *
      (C (P : Matrix n n k) * (Z : Matrix n n (LaurentLogBase k)) * C (↑P⁻¹ : Matrix n n k))
  have hzP : matrixDerivative d (C (P : Matrix n n k)) = 0 := matrixDerivative_constant d _
  have hzPi : matrixDerivative d (C (↑P⁻¹ : Matrix n n k)) = 0 := matrixDerivative_constant d _
  simp only [matrixDerivative_mul, hzP, hzPi, zero_mul, mul_zero,
    add_zero, zero_add, hZ]
  change C (P : Matrix n n k) * (C A * (Z : Matrix n n (LaurentLogBase k))) *
    C (↑P⁻¹ : Matrix n n k) = _
  simp only [map_mul, mul_assoc]
  rw [← mul_assoc (C (↑P⁻¹ : Matrix n n k)), hC, one_mul]

omit [CharZero k] in
/-- Constant matrices evaluate back to themselves at t=1, ell=0. -/
theorem stage15_constant_matrix_at_point (P : Matrix n n k) :
    (laurentLogBasePoint k).toRingHom.mapMatrix (ramifiedConstantMatrix P) = P := by
  ext i j
  exact (laurentLogBasePoint k).commutes (P i j)

omit [CharZero k] in
/-- Normalization at the algebraic base point survives constant conjugation. -/
theorem stage15_constant_conjugation_at_point (P : (Matrix n n k)ˣ)
    (Z : (Matrix n n (LaurentLogBase k))ˣ)
    (hZ : (laurentLogBasePoint k).toRingHom.mapMatrix
      (Z : Matrix n n (LaurentLogBase k)) = 1) :
    (laurentLogBasePoint k).toRingHom.mapMatrix
      (↑(stage15_constant_matrix_unit P * Z * (stage15_constant_matrix_unit P)⁻¹) :
        Matrix n n (LaurentLogBase k)) = 1 := by
  change (laurentLogBasePoint k).toRingHom.mapMatrix
    (ramifiedConstantMatrix (P : Matrix n n k) * (Z : Matrix n n (LaurentLogBase k)) *
      ramifiedConstantMatrix (↑P⁻¹ : Matrix n n k)) = 1
  rw [map_mul, map_mul, stage15_constant_matrix_at_point, stage15_constant_matrix_at_point,
    hZ, mul_one, Units.mul_inv]

/-- Every constant matrix whose minimal-polynomial roots are rational admits an
actual fundamental matrix unit after positive ramification. The unit is
normalized at t=1, ell=0 and solves the manuscript's exact derivation. -/
theorem stage15_rational_matrix_fundamental_unit [IsAlgClosed k]
    (M : Matrix n n k)
    (hrat : ∀ a : k, (minpoly k M).IsRoot a → ∃ q : ℚ, (q : k) = a) :
    ∃ N : ℕ, 0 < N ∧ ∃ Y : (Matrix n n (LaurentLogBase k))ˣ,
      matrixDerivative (manuscriptBaseDerivation (k := k) N)
        (Y : Matrix n n (LaurentLogBase k)) =
        ramifiedConstantMatrix M * (Y : Matrix n n (LaurentLogBase k)) ∧
      (laurentLogBasePoint k).toRingHom.mapMatrix
        (Y : Matrix n n (LaurentLogBase k)) = 1 := by
  obtain ⟨P, q, J, hn, hc, hconj⟩ := stage15_rational_matrix_conjugation M hrat
  obtain ⟨N, hN, Z, hODE, hpoint⟩ := rational_commuting_fundamental_unit q J hn hc
  let A : Matrix n n k := Matrix.diagonal (fun i => (q i : k)) + J
  have hA : ramifiedConstantMatrix A =
      Matrix.diagonal (fun i => algebraMap k (LaurentLogBase k) (q i : k)) +
        ramifiedConstantMatrix J := by
    simp only [A, ramifiedConstantMatrix, map_add, RingHom.mapMatrix_apply,
      Matrix.diagonal_map (map_zero (algebraMap k (LaurentLogBase k)))]
  have hM : (P : Matrix n n k) * A * (↑P⁻¹ : Matrix n n k) = M := by
    change (P : Matrix n n k) * (Matrix.diagonal (fun i => (q i : k)) + J) *
      (↑P⁻¹ : Matrix n n k) = M
    rw [← hconj]
    simp only [← mul_assoc, Units.mul_inv, one_mul]
    rw [mul_assoc, Units.mul_inv, mul_one]
  refine ⟨N, hN, stage15_constant_matrix_unit P * Z * (stage15_constant_matrix_unit P)⁻¹,
    ?_, stage15_constant_conjugation_at_point P Z hpoint⟩
  have hODE' : matrixDerivative (manuscriptBaseDerivation (k := k) N)
      (Z : Matrix n n (LaurentLogBase k)) =
      ramifiedConstantMatrix A * (Z : Matrix n n (LaurentLogBase k)) := by
    rw [hA]; exact hODE
  simpa only [hM] using stage15_constant_conjugation_derivative
    (manuscriptBaseDerivation (k := k) N) P A Z hODE'

end StrictEUnit
