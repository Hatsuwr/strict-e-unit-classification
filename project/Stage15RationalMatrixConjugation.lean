import Stage15RationalJordanDecomposition
import Mathlib.LinearAlgebra.Matrix.Basis

/-! Actual invertible constant conjugating matrices for rational spectrum. -/
noncomputable section
namespace StrictEUnit
open Module
variable {k n : Type*} [Field k] [CharZero k] [Fintype n] [DecidableEq n]

/-- Convert a basis of coordinate space to the actual change-of-basis unit. -/
def stage15_basis_matrix_unit (b : Basis n k (n → k)) : (Matrix n n k)ˣ where
  val := (Pi.basisFun k n).toMatrix b
  inv := b.toMatrix (Pi.basisFun k n)
  val_inv := Basis.toMatrix_mul_toMatrix_flip _ _
  inv_val := Basis.toMatrix_mul_toMatrix_flip _ _

omit [CharZero k] in
/-- This unit conjugates the input matrix to its matrix in the supplied basis. -/
theorem stage15_basis_matrix_conjugates (M : Matrix n n k) (b : Basis n k (n → k)) :
    (↑(stage15_basis_matrix_unit b)⁻¹ : Matrix n n k) * M *
      (stage15_basis_matrix_unit b : Matrix n n k) =
      LinearMap.toMatrixAlgEquiv b (Matrix.toLinAlgEquiv (Pi.basisFun k n) M) := by
  change b.toMatrix (Pi.basisFun k n) * M * (Pi.basisFun k n).toMatrix b = _
  have h := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b
    (Pi.basisFun k n) b (Pi.basisFun k n)
    (Matrix.toLinAlgEquiv (Pi.basisFun k n) M)
  change b.toMatrix (Pi.basisFun k n) *
    LinearMap.toMatrixAlgEquiv (Pi.basisFun k n)
      (Matrix.toLinAlgEquiv (Pi.basisFun k n) M) *
    (Pi.basisFun k n).toMatrix b = _ at h
  simpa only [LinearMap.toMatrixAlgEquiv_toLinAlgEquiv] using h

/-- A precise checkable rational-spectrum condition, stated on the input
matrix's minimal polynomial, produces an actual invertible conjugating matrix.
Algebraic closedness ensures splitting; every root is required to be rational. -/
theorem stage15_rational_matrix_conjugation [IsAlgClosed k]
    (M : Matrix n n k)
    (hrat : ∀ a : k, (minpoly k M).IsRoot a → ∃ q : ℚ, (q : k) = a) :
    ∃ (P : (Matrix n n k)ˣ) (q : n → ℚ) (J : Matrix n n k),
      IsNilpotent J ∧ Commute (Matrix.diagonal fun i => (q i : k)) J ∧
      (↑P⁻¹ : Matrix n n k) * M * (P : Matrix n n k) =
        Matrix.diagonal (fun i => (q i : k)) + J := by
  let e := Matrix.toLinAlgEquiv (Pi.basisFun k n)
  have hspec (a : k) (ha : Module.End.HasEigenvalue (e M) a) : ∃ q : ℚ, (q : k) = a := by
    apply hrat a
    have hroot := Module.End.isRoot_of_hasEigenvalue ha
    simpa only [minpoly.algEquiv_eq] using hroot
  obtain ⟨b, q, J, hn, hc, hdecomp⟩ := stage15_rational_jordan_decomposition (e M) hspec
  refine ⟨stage15_basis_matrix_unit b, q, J, hn, hc, ?_⟩
  rw [stage15_basis_matrix_conjugates]
  exact hdecomp

end StrictEUnit
