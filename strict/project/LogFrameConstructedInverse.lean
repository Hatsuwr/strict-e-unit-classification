import LogFrameDeterminantDifferential
import LogFirstOrderLeadingUnit
import LogFrameFiniteBounds
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- A NONZERO determinant of an actual twisted log-solution frame is a unit
in polynomial-valued Laurent series. Nonvanishing is explicit; it is not
inferred from the differential equation or from a selected-family assertion. -/
theorem logFrame_coefficient_determinant_isUnit {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (rho : Fin r → K)
    (Y : Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries K)))
    (hY : ∀ j i,twistedLogPolynomialEuler (rho j) (Y i j)=
      ∑ l,logPowerSeriesEmbedding (C i l)*Y l j) (hdet : Y.det≠0) :
    IsUnit (Matrix.of (fun i j =>logPolynomialToCoefficientSeries (Y i j))).det := by
  have h := logFirstOrder_coefficient_series_isUnit Y.det
    (C.trace-PowerSeries.C K (∑ j,rho j)) hdet
    (logFrame_determinant_equation C rho Y hY)
  rw [RingHom.map_det] at h
  exact h

/-- Construct BOTH inverses in the required ring, along with a fixed pole
bound. No inverse, localization in log, or inverse arithmetic is assumed. -/
theorem logFrame_exists_inverse_with_fixed_pole_bound {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (rho : Fin r → K)
    (Y : Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries K)))
    (hY : ∀ j i,twistedLogPolynomialEuler (rho j) (Y i j)=
      ∑ l,logPowerSeriesEmbedding (C i l)*Y l j) (hdet : Y.det≠0) :
    ∃ J : Matrix (Fin r) (Fin r) (LaurentSeries (Polynomial K)),∃ W : ℕ,
      (Matrix.of (fun i j =>logPolynomialToCoefficientSeries (Y i j)))*J=1 ∧
      J*(Matrix.of (fun i j =>logPolynomialToCoefficientSeries (Y i j)))=1 ∧
      (∀ i j a,a< -(W : ℤ) →(J i j).coeff a=0) := by
  let H := Matrix.of (fun i j =>logPolynomialToCoefficientSeries (Y i j))
  have hu : IsUnit H.det := logFrame_coefficient_determinant_isUnit C rho Y hY hdet
  obtain ⟨W,hW⟩ := laurentMatrix_exists_fixed_pole_bound H⁻¹
  exact ⟨H⁻¹,W,Matrix.mul_nonsing_inv H hu,Matrix.nonsing_inv_mul H hu,hW⟩

end StrictEUnit
end
