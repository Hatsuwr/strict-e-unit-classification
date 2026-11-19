import FundamentalMatrixConstants

noncomputable section
namespace StrictEUnit

variable {k R n : Type*} [CommRing k] [CommRing R] [Algebra k R]
  [Fintype n] [DecidableEq n]

/-- For an invertible fundamental matrix, a solution vector has horizontal
coordinates. Unlike the transition between fundamental matrices, the vector
needs no inverse or determinant, and it can come from a different algebra. -/
theorem v5_horizontal_coordinates (δ : Derivation k R R)
    (A : Matrix n n R) (Y : (Matrix n n R)ˣ) (v : n → R)
    (hY : matrixDerivative δ (Y : Matrix n n R) = A * (Y : Matrix n n R))
    (hv : ∀ i, δ (v i) = (A.mulVec v) i) :
    (∀ i, δ (((↑Y⁻¹ : Matrix n n R).mulVec v) i) = 0) ∧
      (Y : Matrix n n R).mulVec ((↑Y⁻¹ : Matrix n n R).mulVec v) = v := by
  classical
  -- Each column of Z is v. Applying the existing matrix constant transition
  -- to this (possibly singular) solution matrix gives the vector statement.
  let Z : Matrix n n R := fun i _ => v i
  have hZ : matrixDerivative δ Z = A * Z := by
    ext i j
    simpa only [matrixDerivative_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, Z]
      using hv i
  have hd := fundamental_matrix_transition_constant δ A Y Z hY hZ
  constructor
  · intro i
    simpa only [matrixDerivative_apply, Matrix.mul_apply, Matrix.zero_apply,
      Matrix.mulVec, dotProduct, Z] using congrArg (fun M : Matrix n n R => M i i) hd
  · rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

end StrictEUnit
#print axioms StrictEUnit.v5_horizontal_coordinates
