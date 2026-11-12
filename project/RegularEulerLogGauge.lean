import EulerCyclicCompanionIdentity
import LogFrameDeterminantDifferential

noncomputable section
open scoped BigOperators Classical Matrix
namespace StrictEUnit

/-- Differential, not algebraic, conjugacy, including a right exponent matrix. -/
theorem matrix_twoSided_gauge_iff {k R ι : Type*} [CommRing k] [CommRing R]
    [Algebra k R] [Fintype ι] [DecidableEq ι] (D : Derivation k R R)
    (A B G H X S : Matrix ι ι R) (hHG : H*G=1)
    (hc : matrixDerivative D G+G*A=B*G) :
    matrixDerivative D X=A*X-X*S ↔
      matrixDerivative D (G*X)=B*(G*X)-(G*X)*S := by
  have hc' : matrixDerivative D G=B*G-G*A := eq_sub_iff_add_eq.mpr hc
  rw [matrixDerivative_mul,hc']
  constructor
  · intro h;rw [h];noncomm_ring
  · intro h
    have he : G*matrixDerivative D X=G*(A*X-X*S) := by
      calc
        _=(B*(G*X)-(G*X)*S)-(B*G-G*A)*X := (eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using h))
        _=_ := by noncomm_ring
    have hi := congrArg (fun M =>H*M) he
    simpa only [← mul_assoc,hHG,one_mul] using hi

variable {K : Type*} [Field K] [CharZero K]
local instance : SMul K (Polynomial (LaurentSeries K)) := Algebra.toSMul
local instance : Module K (Polynomial (LaurentSeries K)) := Algebra.toModule

theorem logFrame_matrix_equation_iff {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (rho : Fin r →K)
    (Y : Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries K))) :
    (∀ j i,twistedLogPolynomialEuler (rho j) (Y i j)=
      ∑ l,logPowerSeriesEmbedding (C i l)*Y l j) ↔
    matrixDerivative (k:=K) (logFrameAlgebraDerivation (K:=K)) Y=
      (C.map logPowerSeriesEmbedding)*Y-
        Y*(Matrix.diagonal (fun j =>Polynomial.C (HahnSeries.C (rho j)))) := by
  constructor
  · exact logFrame_actual_matrix_equation C rho Y
  · intro h j i
    have hi := congrFun (congrFun h i) j
    simp only [matrixDerivative_apply,logFrameAlgebraDerivation_apply,Matrix.sub_apply,
      Matrix.mul_apply,Matrix.map_apply,Matrix.diagonal_apply,mul_ite,mul_zero,
      Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hi
    rw [twistedLogPolynomialEuler_ring_formula,hi]
    ring

/-- The coefficient embedding intertwines the actual regular and log derivations. -/
theorem logPowerSeriesEmbedding_euler (f : PowerSeries K) :
    logFrameAlgebraDerivation (logPowerSeriesEmbedding f)=
      logPowerSeriesEmbedding (powerSeriesEuler f) := by
  rw [logFrameAlgebraDerivation_apply]
  change logPolynomialEuler 1 (Polynomial.C (HahnSeries.ofPowerSeries ℤ K f))=_
  rw [logPolynomialEuler_C,← powerSeriesEuler_laurent]
  rfl

/-- The logarithmic connection identity transports in BOTH directions under a
proved regular gauge. No assertion about an ordinary solution is used. -/
theorem regularEuler_log_frame_gauge_iff {r : ℕ}
    (C B G H : Matrix (Fin r) (Fin r) (PowerSeries K)) (hHG : H*G=1)
    (hc : Matrix.of (fun i j =>powerSeriesEuler (G i j))+G*C=B*G)
    (rho : Fin r →K) (Y : Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries K))) :
    (∀ j i,twistedLogPolynomialEuler (rho j) (Y i j)=
      ∑ l,logPowerSeriesEmbedding (C i l)*Y l j) ↔
    (∀ j i,twistedLogPolynomialEuler (rho j) ((G.map logPowerSeriesEmbedding*Y) i j)=
      ∑ l,logPowerSeriesEmbedding (B i l)*(G.map logPowerSeriesEmbedding*Y) l j) := by
  rw [logFrame_matrix_equation_iff,logFrame_matrix_equation_iff]
  refine matrix_twoSided_gauge_iff (logFrameAlgebraDerivation (K:=K)) _ _ _
    (H.map logPowerSeriesEmbedding) _ _ ?_ ?_
  · change logPowerSeriesEmbedding.toRingHom.mapMatrix H *
      logPowerSeriesEmbedding.toRingHom.mapMatrix G=1
    rw [← map_mul,hHG,map_one]
  · funext i j
    have h := congrArg (logPowerSeriesEmbedding (K:=K)) (congrFun (congrFun hc i) j)
    simpa only [Matrix.add_apply,Matrix.mul_apply,Matrix.map_apply,Matrix.of_apply,
      matrixDerivative_apply,logPowerSeriesEmbedding_euler,map_add,map_sum,map_mul] using h

end StrictEUnit
end
