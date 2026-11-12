import FiniteLogMatrixExponentialEquation
import RamifiedBaseManuscriptODE

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K I : Type*} [Field K] [CharZero K] [Fintype I] [DecidableEq I]

/-- The finite polynomial log exponential used in the actual amplitudes maps
to the very same finite log factor in the exact Laurent-log base ring. -/
theorem finiteLogMatrixExponential_map_base
    (J : Matrix I I K) (hJ : IsNilpotent J) :
    (Polynomial.mapRingHom (algebraMap K (LaurentPolynomial K))).mapMatrix
      (finiteLogMatrixExponential J) = (ramifiedLogUnit J hJ).val := by
  let f := Polynomial.mapRingHom (algebraMap K (LaurentPolynomial K))
  have hg : f.mapMatrix (finiteLogMatrixGenerator J) = ramifiedLogExponent J := by
    ext i j
    simp only [finiteLogMatrixGenerator, ramifiedLogExponent, ramifiedConstantMatrix,
      RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    simp [f, Polynomial.algebraMap_apply]
  have hm := (finiteLogMatrixGenerator_nilpotent J hJ).map_exp f.mapMatrix
  change f.mapMatrix (IsNilpotent.exp (finiteLogMatrixGenerator J)) = _
  rw [hm, hg]
  rfl

/-- A fixed integer external power and the actual finite logarithmic factor
form a unit in LaurentLogBase, not merely in a larger Laurent-series ring. -/
def fixedExponentBaseUnit (m : ℤ) (J : Matrix I I K) (hJ : IsNilpotent J) :
    (Matrix I I (LaurentLogBase K))ˣ := ramifiedBaseMatrix (fun _ => m) J hJ

/-- Literal manuscript-scale equation for a fixed external exponent. -/
theorem fixedExponentBaseUnit_equation
    (N : ℕ) (hN : N ≠ 0) (m : ℤ) (xi : K) (hxi : (m : K) / (N : K) = xi)
    (J : Matrix I I K) (hJ : IsNilpotent J) :
    matrixDerivative (manuscriptBaseDerivation N) (fixedExponentBaseUnit m J hJ).val =
      ramifiedConstantMatrix (Matrix.diagonal (fun _ => xi) + J) *
        (fixedExponentBaseUnit m J hJ).val := by
  have hw : RespectsRamifiedWeights (fun _ : I => m) J := by
    intro i j h
    exact (h rfl).elim
  have h := ramifiedBaseMatrix_manuscript_derivative N hN (fun _ : I => m) J hJ hw
  simpa only [hxi, fixedExponentBaseUnit, ramifiedConstantMatrix, map_add,
    RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero _)] using h

end StrictEUnit
end
