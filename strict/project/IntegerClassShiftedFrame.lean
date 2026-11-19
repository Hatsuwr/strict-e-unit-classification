import IntegerClassAlignedRepresentatives
import FrobeniusIntegerShiftEquation
import FiniteSplittingArithmeticFrame

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

/-- Literal column shifts preserve the actual differential system, with
exactly the corresponding change in its external exponents. -/
theorem integerShift_logFrame_equation {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K))
    (rho sigma : Fin r → K) (shift : Fin r → ℤ)
    (hs : ∀ j,rho j=sigma j+(shift j : K))
    (Y : Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries K)))
    (hY : ∀ j i,twistedLogPolynomialEuler (rho j) (Y i j)=
      ∑ l,logPowerSeriesEmbedding (C i l)*Y l j) :
    ∀ j i,twistedLogPolynomialEuler (sigma j) (frobeniusIntegerShift (shift j) (Y i j))=
      ∑ l,logPowerSeriesEmbedding (C i l)*frobeniusIntegerShift (shift j) (Y l j) := by
  intro j i
  rw [frobeniusIntegerShift_twistedEuler,← hs j,hY j i]
  simp only [frobeniusIntegerShift,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  ring

/-- Multiplication of each column by a nonzero Laurent monomial preserves
the frame determinant. No new linear-independence premise is imposed. -/
theorem integerShift_logFrame_det_nonzero {r : ℕ}
    (shift : Fin r → ℤ)
    (Y : Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries K))) (hY : Y.det≠0) :
    (Matrix.of fun i j =>frobeniusIntegerShift (shift j) (Y i j)).det≠0 := by
  classical
  let v : Fin r →Polynomial (LaurentSeries K) := fun j =>Polynomial.C (HahnSeries.single (shift j) (1 : K))
  have hv : ∀ j,v j≠0 := by
    intro j
    simp [v,Polynomial.C_ne_zero,HahnSeries.single_ne_zero]
  have h := Matrix.det_mul_column v Y.transpose
  have he : (Matrix.of fun i j =>frobeniusIntegerShift (shift j) (Y i j)).det=
      (∏ j,v j)*Y.det := by
    rw [← Matrix.det_transpose]
    exact h.trans (by rw [Matrix.det_transpose])
  rw [he]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun j _ =>hv j)) hY

end StrictEUnit
end
