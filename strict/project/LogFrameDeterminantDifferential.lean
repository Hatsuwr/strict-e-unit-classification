import DeterminantalIdealStability
import LogSolutionConnectionIntertwining
import Mathlib.LinearAlgebra.Matrix.Trace

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

/-- Left multiplication contributes trace A to determinant variation. -/
theorem logFrame_determinant_left_variation_eq_trace_mul {R n : Type*}
    [CommRing R] [Fintype n] [DecidableEq n] (A F : Matrix n n R) :
    (∑ i, (F.updateRow i (fun j => (A * F) i j)).det) = A.trace * F.det := by
  rw [Matrix.trace, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hrow : (fun j => (A * F) i j) = ∑ k, A i k • F k := by
    ext j
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hrow, Matrix.det_updateRow_sum, smul_eq_mul]
  rfl

/-- Right multiplication contributes trace C to determinant variation. -/
theorem logFrame_determinant_right_variation_eq_trace_mul {R n : Type*}
    [CommRing R] [Fintype n] [DecidableEq n] (C F : Matrix n n R) :
    (∑ j, (F.updateCol j (fun i => (F * C) i j)).det) = C.trace * F.det := by
  rw [Matrix.trace, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have hcol : (fun i => (F * C) i j) = fun i => ∑ k, C k j • F i k := by
    ext i
    simp only [Matrix.mul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro k hk
    exact mul_comm _ _
  rw [hcol, Matrix.det_updateCol_sum, smul_eq_mul]
  rfl

/-- Abel's determinant equation for a genuine two-sided matrix equation,
without assuming that the solution matrix is invertible. -/
theorem logFrame_derivation_det_two_sided {k R n : Type*}
    [CommRing k] [CommRing R] [Algebra k R] [Fintype n] [DecidableEq n]
    (δ : Derivation k R R) (A C F : Matrix n n R)
    (hF : matrixDerivative δ F = A * F - F * C) :
    δ F.det = (A.trace - C.trace) * F.det := by
  rw [derivation_det_rows]
  have hrow (i : n) : (fun j => δ (F i j)) =
      (fun j => (A * F) i j) - (fun j => (F * C) i j) := by
    ext j
    exact congrArg (fun M => M i j) hF
  have hsub (i : n) (u v : n → R) :
      (F.updateRow i (u-v)).det = (F.updateRow i u).det - (F.updateRow i v).det :=
    Matrix.detRowAlternating.map_update_sub F i u v
  simp_rw [hrow, hsub]
  rw [Finset.sum_sub_distrib,
    ← determinant_variation_rows_cols F (F * C),
    logFrame_determinant_left_variation_eq_trace_mul, logFrame_determinant_right_variation_eq_trace_mul,
    sub_mul]

variable {K : Type*} [Field K] [CharZero K]

local instance : SMul K (Polynomial (LaurentSeries K)) := Algebra.toSMul
local instance : Module K (Polynomial (LaurentSeries K)) := Algebra.toModule

/-- The product rule as a separate function statement avoids module diamonds. -/
theorem logFrameEuler_leibniz (f g : Polynomial (LaurentSeries K)) :
    logPolynomialEuler 1 (f*g)=f*logPolynomialEuler 1 g+g*logPolynomialEuler 1 f := by
  rw [logPolynomialEuler_mul]
  ring

/-- Rebundle the same Euler function with the canonical scalar module. -/
def logFrameAlgebraDerivation : Derivation K (Polynomial (LaurentSeries K)) (Polynomial (LaurentSeries K)) where
  toLinearMap := literalTwistedEulerLinear 0
  map_one_eq_zero' := by
    change twistedLogPolynomialEuler 0 1=0
    rw [twistedLogPolynomialEuler_ring_formula,map_zero,map_zero,zero_mul,add_zero]
    simpa only [map_one] using logPolynomialEuler_algebraMap (1 : K) 1
  leibniz' f g := by
    change twistedLogPolynomialEuler 0 (f*g)=f*twistedLogPolynomialEuler 0 g+g*twistedLogPolynomialEuler 0 f
    simp only [twistedLogPolynomialEuler_ring_formula,map_zero,zero_mul,add_zero]
    exact logFrameEuler_leibniz f g

@[simp] theorem logFrameAlgebraDerivation_apply (f : Polynomial (LaurentSeries K)) :
    logFrameAlgebraDerivation f=logPolynomialEuler 1 f := by
  change twistedLogPolynomialEuler 0 f=logPolynomialEuler 1 f
  simp only [twistedLogPolynomialEuler_ring_formula,map_zero,zero_mul,add_zero]

/-- The actual log-solution matrix obeys the two-sided equation with the
class exponents on the RIGHT. No determinant nonvanishing is required. -/
theorem logFrame_actual_matrix_equation {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (rho : Fin r → K)
    (Y : Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries K)))
    (hY : ∀ j i,twistedLogPolynomialEuler (rho j) (Y i j)=
      ∑ l,logPowerSeriesEmbedding (C i l)*Y l j) :
    matrixDerivative (k:=K) (R:=Polynomial (LaurentSeries K)) (logFrameAlgebraDerivation (K:=K)) Y=
      (C.map logPowerSeriesEmbedding)*Y-Y*(Matrix.diagonal (fun j =>Polynomial.C (HahnSeries.C (rho j)))) := by
  funext i j
  have h := hY j i
  rw [twistedLogPolynomialEuler_ring_formula] at h
  rw [matrixDerivative_apply,logFrameAlgebraDerivation_apply]
  simp only [Matrix.sub_apply,Matrix.mul_apply,Matrix.diagonal_apply]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  exact (eq_sub_iff_add_eq.mpr h).trans (by congr 1;ring)

/-- Exact scalar equation for the determinant of the actual twisted frame. -/
theorem logFrame_determinant_equation {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (rho : Fin r → K)
    (Y : Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries K)))
    (hY : ∀ j i,twistedLogPolynomialEuler (rho j) (Y i j)=
      ∑ l,logPowerSeriesEmbedding (C i l)*Y l j) :
    logPolynomialEuler 1 Y.det=
      logPowerSeriesEmbedding (C.trace-PowerSeries.C K (∑ j,rho j))*Y.det := by
  have h := logFrame_derivation_det_two_sided (k:=K) (R:=Polynomial (LaurentSeries K)) (n:=Fin r) (logFrameAlgebraDerivation (K:=K))
    (C.map logPowerSeriesEmbedding) (Matrix.diagonal (fun j =>Polynomial.C (HahnSeries.C (rho j)))) Y
    (logFrame_actual_matrix_equation C rho Y hY)
  rw [logFrameAlgebraDerivation_apply] at h
  rw [h]
  congr 1
  simp only [Matrix.trace,Matrix.diag,Matrix.map_apply,Matrix.diagonal_apply,ite_true,
    map_sub,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  change Polynomial.C (HahnSeries.C (rho j))=
    Polynomial.C (HahnSeries.ofPowerSeries ℤ K (PowerSeries.C K (rho j)))
  rw [HahnSeries.ofPowerSeries_C]


end StrictEUnit
end
