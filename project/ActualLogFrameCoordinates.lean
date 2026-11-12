import ShiftedDifferentialFrameCoordinates
import CoefficientEulerEigenvectors

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Actual coefficient-ring coordinates of every twisted solution of a
supplied genuine invertible source frame obey diagonal Euler equations. -/
theorem actualLogFrame_coordinates {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (rho : Fin r → K)
    (Y : Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries K)))
    (hY : ∀ j i,twistedLogPolynomialEuler (rho j) (Y i j)=
      ∑ l,logPowerSeriesEmbedding (C i l)*Y l j) (hdet : Y.det≠0)
    (xi : K) (u : Fin r →LaurentSeries (Polynomial K))
    (hu : ∀ i,twistedPolynomialCoefficientEuler xi (u i)=
      ∑ j,logPolynomialToCoefficientSeries (logPowerSeriesEmbedding (C i j))*u j) :
    ∃ v : Fin r →LaurentSeries (Polynomial K),
      (∀ i, u i=∑ j,logPolynomialToCoefficientSeries (Y i j)*v j) ∧
      (∀ j,polynomialCoefficientEuler 1 (v j)=(rho j-xi) • v j) := by
  let H : Matrix (Fin r) (Fin r) (LaurentSeries (Polynomial K)) :=
    fun i j =>logPolynomialToCoefficientSeries (Y i j)
  let A : Matrix (Fin r) (Fin r) (LaurentSeries (Polynomial K)) :=
    fun i j =>logPolynomialToCoefficientSeries (logPowerSeriesEmbedding (C i j))
  let rr : Fin r →LaurentSeries (Polynomial K) :=fun j =>HahnSeries.single 0 (Polynomial.C (rho j))
  let xx : LaurentSeries (Polynomial K) :=HahnSeries.single 0 (Polynomial.C xi)
  obtain ⟨J,W,hHJ,hJH,hW⟩ := logFrame_exists_inverse_with_fixed_pole_bound C rho Y hY hdet
  have hdH : (fun i j =>coefficientEulerAdd (H i j))=A*H-H*Matrix.diagonal rr := by
    funext i j
    have he := congrArg logPolynomialToCoefficientSeries (hY j i)
    rw [logPolynomialToCoefficientSeries_twistedEuler] at he
    simp only [map_sum,map_mul,twistedPolynomialCoefficientEuler,laurentCoefficient_smul_eq_mul] at he
    change polynomialCoefficientEuler 1 (H i j)+rr j*H i j=∑ l,A i l*H l j at he
    change polynomialCoefficientEuler 1 (H i j)=(A*H) i j-(H*Matrix.diagonal rr) i j
    rw [Matrix.mul_diagonal]
    exact (eq_sub_iff_add_eq.mpr he).trans (by rw [mul_comm]; rfl)
  have hdu : ∀ i,coefficientEulerAdd (u i)=A.mulVec u i-xx*u i := by
    intro i
    have he := hu i
    rw [twistedPolynomialCoefficientEuler,laurentCoefficient_smul_eq_mul] at he
    exact eq_sub_iff_add_eq.mpr he
  obtain ⟨hv,hdv⟩ := shiftedDifferentialFrame_coordinates coefficientEulerAdd
    coefficientLaurentEuler_mul A H J rr xx hJH hHJ hdH u hdu
  refine ⟨J.mulVec u,?_,?_⟩
  · intro i
    exact (congrFun hv i).symm
  · intro j
    have he := hdv j
    change polynomialCoefficientEuler 1 (J.mulVec u j)=(rr j-xx)*J.mulVec u j at he
    rw [laurentCoefficient_smul_eq_mul]
    convert he using 1
    simp only [rr,xx,← HahnSeries.C_apply,map_sub]

end StrictEUnit
end
