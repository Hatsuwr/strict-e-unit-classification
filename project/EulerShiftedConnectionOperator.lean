import NormalizedFallingShift
import EulerFallingConnectionArithmetic

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

def powerSeriesEulerRowConnection {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) : Module.End K (Fin r → PowerSeries K) where
  toFun v j := powerSeriesEuler (v j)+∑ l,v l*C l j
  map_add' v w := by
    funext j
    change powerSeriesEulerLinear (v j+w j)+(∑ l,(v l+w l)*C l j)=_
    simp only [map_add,Pi.add_apply,add_mul,Finset.sum_add_distrib,powerSeriesEulerLinear_apply]
    abel
  map_smul' c v := by
    funext j
    change powerSeriesEulerLinear (c • v j)+(∑ l,(c • v l)*C l j)=c • (powerSeriesEulerLinear (v j)+∑ l,v l*C l j)
    rw [map_smul]
    simp only [smul_add,Finset.smul_sum,Algebra.smul_def,mul_assoc,mul_add,Finset.mul_sum]

omit [CharZero K] in
theorem powerSeriesEulerRowConnection_falling {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (m : ℕ) (i : Fin r) :
    Polynomial.aeval (powerSeriesEulerRowConnection C) (descPochhammer K m)
      (fun j => (1 : Matrix (Fin r) (Fin r) (PowerSeries K)) i j)=
        fun j => powerSeriesEulerFallingConnection C m i j := by
  induction m with
  | zero => simp only [descPochhammer_zero,map_one,Module.End.one_apply,powerSeriesEulerFallingConnection]
  | succ m ih =>
    have hp : descPochhammer K (m+1)=(Polynomial.X-Polynomial.C (m : K))*descPochhammer K m := by
      rw [descPochhammer_succ_right,Polynomial.C_eq_natCast,mul_comm]
    rw [hp,map_mul,Module.End.mul_apply,ih]
    simp only [map_sub,Polynomial.aeval_X,Polynomial.aeval_C,LinearMap.sub_apply,
      Module.algebraMap_end_apply]
    funext j
    change powerSeriesEuler (powerSeriesEulerFallingConnection C m i j)+
      (∑ l,powerSeriesEulerFallingConnection C m i l*C l j)-
        (m : K) • powerSeriesEulerFallingConnection C m i j=_
    simp only [powerSeriesEulerFallingConnection,Algebra.smul_def,map_natCast]

omit [CharZero K] in
theorem powerSeriesEulerRowConnection_divided {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (m : ℕ) (i : Fin r) :
    Polynomial.aeval (powerSeriesEulerRowConnection C) (normalizedFallingSymbol (K:=K) m)
      (fun j => (1 : Matrix (Fin r) (Fin r) (PowerSeries K)) i j)=
        fun j => powerSeriesEulerDividedConnection C m i j := by
  rw [normalizedFallingSymbol,map_mul,Module.End.mul_apply,Polynomial.aeval_C,
    Module.algebraMap_end_apply,powerSeriesEulerRowConnection_falling]
  funext j
  simp only [Pi.smul_apply,powerSeriesEulerDividedConnection,PowerSeries.smul_eq_C_mul]

/-- Explicit coefficient expression for the actual exponent-shifted operator. -/
def powerSeriesEulerShiftedDividedConnection {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (rho : K) (m : ℕ) :
    Matrix (Fin r) (Fin r) (PowerSeries K) := fun i j =>
  ∑ ab ∈ Finset.antidiagonal m,PowerSeries.C K (Ring.choose (-rho) ab.1)*
    powerSeriesEulerDividedConnection C ab.2 i j

/-- This is literally binom(connection-rho,m), not an arithmetic surrogate. -/
theorem powerSeriesEulerShiftedDividedConnection_operator {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (rho : K) (m : ℕ) (i : Fin r) :
    Polynomial.aeval (powerSeriesEulerRowConnection C-rho • (1 : Module.End K (Fin r → PowerSeries K)))
      (normalizedFallingSymbol (K:=K) m)
      (fun j => (1 : Matrix (Fin r) (Fin r) (PowerSeries K)) i j)=
        fun j => powerSeriesEulerShiftedDividedConnection C rho m i j := by
  have he : powerSeriesEulerRowConnection C-rho • (1 : Module.End K (Fin r → PowerSeries K))=
      powerSeriesEulerRowConnection C+algebraMap K (Module.End K (Fin r → PowerSeries K)) (-rho) := by
    rw [map_neg,Module.algebraMap_end_eq_smul_id,sub_eq_add_neg]
    rfl
  rw [he,normalizedFallingSymbol_aeval_translate]
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,powerSeriesEulerRowConnection_divided]
  funext j
  simp only [Finset.sum_apply,Pi.smul_apply,powerSeriesEulerShiftedDividedConnection]
  simp only [PowerSeries.smul_eq_C_mul]

end StrictEUnit
end
