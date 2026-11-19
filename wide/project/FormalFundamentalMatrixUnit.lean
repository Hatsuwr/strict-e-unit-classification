import FormalFundamentalMatrix
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
NEW SOURCE-ONLY: invertibility is derived from W(0)=I. No invertibility,
nonzero-determinant, analytic convergence, or Picard--Vessiot premise is added.
The ordinary-point rational translation and stable graph descent are separate.
-/
noncomputable section
open scoped Matrix
namespace StrictEUnit

variable {K : Type*} [Field K] {r : ℕ}

/-- The determinant has constant coefficient one, not merely a supplied
nonvanishing constant. This also holds for r=0. -/
theorem formalFundamentalMatrix_det_constantCoeff
    (A : Matrix (Fin r) (Fin r) (PowerSeries K)) :
    PowerSeries.constantCoeff K (formalFundamentalMatrix A).det = 1 := by
  rw [(PowerSeries.constantCoeff K).map_det]
  change ((formalFundamentalMatrix A).map (PowerSeries.constantCoeff K)).det = 1
  rw [formalFundamentalMatrix_constantCoeff, Matrix.det_one]

/-- Actual invertibility over K[[z]], derived by the determinant unit criterion
and the power-series constant coefficient unit criterion. -/
theorem formalFundamentalMatrix_isUnit
    (A : Matrix (Fin r) (Fin r) (PowerSeries K)) :
    IsUnit (formalFundamentalMatrix A) := by
  apply (Matrix.isUnit_iff_isUnit_det _).2
  apply PowerSeries.isUnit_iff_constantCoeff.2
  rw [formalFundamentalMatrix_det_constantCoeff]
  exact isUnit_one

/-- An arbitrary characteristic-zero power-series matrix has a normalized
invertible formal fundamental matrix, explicitly constructed above. -/
theorem exists_normalized_formal_fundamentalMatrix [CharZero K]
    (A : Matrix (Fin r) (Fin r) (PowerSeries K)) :
    ∃ W : Matrix (Fin r) (Fin r) (PowerSeries K),
      W.map (PowerSeries.constantCoeff K) = 1 ∧
      W.map (PowerSeries.derivative K) = A * W ∧ IsUnit W := by
  exact ⟨formalFundamentalMatrix A, formalFundamentalMatrix_constantCoeff A,
    formalFundamentalMatrix_derivative A, formalFundamentalMatrix_isUnit A⟩

end StrictEUnit
end
