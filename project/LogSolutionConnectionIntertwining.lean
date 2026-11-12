import AllClassPrefixConnectionArithmetic
import FrobeniusIntegerResonanceSpace

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]
local instance : SMul K (Polynomial (LaurentSeries K)) := Algebra.toSMul
local instance : Module K (Polynomial (LaurentSeries K)) := Algebra.toModule

/-- The actual inclusion of log-free power series in the polynomial-log ring. -/
def logPowerSeriesEmbedding : PowerSeries K →ₐ[K] Polynomial (LaurentSeries K) where
  toRingHom := Polynomial.C.comp (HahnSeries.ofPowerSeries ℤ K)
  commutes' c := by
    change Polynomial.C (HahnSeries.ofPowerSeries ℤ K (PowerSeries.C K c))=algebraMap K _ c
    rw [HahnSeries.ofPowerSeries_C,Polynomial.algebraMap_apply,LaurentSeries.algebraMap_apply]

/-- Reconcile the native log scalar action with its literal constant product. -/
theorem logActualScalar_smul (c : K) (f : Polynomial (LaurentSeries K)) :
    c • f=Polynomial.C (HahnSeries.C c)*f := by
  apply Polynomial.ext
  intro j
  apply HahnSeries.ext
  funext n
  simp only [Polynomial.coeff_smul,Polynomial.coeff_C_mul,HahnSeries.C_apply,
    HahnSeries.coeff_smul,HahnSeries.coeff_single_zero_mul]
  change (algebraMap K (LaurentSeries K) c*f.coeff j).coeff n=c*(f.coeff j).coeff n
  rw [LaurentSeries.algebraMap_apply,HahnSeries.C_apply,HahnSeries.coeff_single_zero_mul]

/-- The captured twisted action has exactly the same constant product. -/
theorem twistedLogPolynomialEuler_ring_formula (rho : K) (f : Polynomial (LaurentSeries K)) :
    twistedLogPolynomialEuler rho f=logPolynomialEuler 1 f+Polynomial.C (HahnSeries.C rho)*f := by
  apply logPolynomialToCoefficientSeries_injective
  rw [logPolynomialToCoefficientSeries_twistedEuler,map_add,map_mul,
    logPolynomialToCoefficientSeries_euler,logPolynomialToCoefficientSeries_C]
  change polynomialCoefficientEuler 1 (logPolynomialToCoefficientSeries f)+
      rho • logPolynomialToCoefficientSeries f=_
  rw [laurentCoefficient_smul_eq_mul]
  congr 2
  apply HahnSeries.ext
  funext n
  simp only [logLaurentCoefficientMap_coeff,HahnSeries.C_apply,HahnSeries.coeff_single]
  split_ifs <;> simp

/-- Twisted Euler is K-linear, not power-series linear. -/
def literalTwistedEulerLinear (rho : K) : Module.End K (Polynomial (LaurentSeries K)) where
  toFun := twistedLogPolynomialEuler rho
  map_add' f g := by
    simp only [twistedLogPolynomialEuler_ring_formula,logPolynomialEuler_add]
    ring
  map_smul' c f := by
    simp only [RingHom.id_apply,twistedLogPolynomialEuler_ring_formula,logActualScalar_smul]
    rw [logPolynomialEuler_mul]
    have hc : logPolynomialEuler 1 (Polynomial.C (HahnSeries.C c))=0 := by
      simpa only [Polynomial.algebraMap_apply,LaurentSeries.algebraMap_apply] using
        logPolynomialEuler_algebraMap (1 : K) c
    rw [hc]
    ring

/-- Leibniz with a LOG-FREE left coefficient, retaining the rho term exactly
once on the right factor. -/
theorem literalTwistedEulerLinear_logfree_mul (rho : K) (a : PowerSeries K)
    (f : Polynomial (LaurentSeries K)) :
    literalTwistedEulerLinear rho (logPowerSeriesEmbedding a*f)=
      logPowerSeriesEmbedding (powerSeriesEuler a)*f+
        logPowerSeriesEmbedding a*literalTwistedEulerLinear rho f := by
  change logPolynomialEuler 1 (Polynomial.C (HahnSeries.ofPowerSeries ℤ K a)*f)+
    rho • (Polynomial.C (HahnSeries.ofPowerSeries ℤ K a)*f)=_
  rw [logPolynomialEuler_mul,logPolynomialEuler_C,← powerSeriesEuler_laurent]
  change Polynomial.C (HahnSeries.ofPowerSeries ℤ K (powerSeriesEuler a))*f+
      Polynomial.C (HahnSeries.ofPowerSeries ℤ K a)*logPolynomialEuler 1 f+
      rho • (Polynomial.C (HahnSeries.ofPowerSeries ℤ K a)*f)=
    Polynomial.C (HahnSeries.ofPowerSeries ℤ K (powerSeriesEuler a))*f+
      Polynomial.C (HahnSeries.ofPowerSeries ℤ K a)*(logPolynomialEuler 1 f+rho • f)
  simp only [Algebra.smul_def]
  ring

/-- Pair a row of ordinary coefficients with a genuine log-solution vector. -/
def logSolutionRowPairing {r : ℕ} (Y : Fin r → Polynomial (LaurentSeries K)) :
    (Fin r → PowerSeries K) →ₗ[K] Polynomial (LaurentSeries K) where
  toFun v := ∑ j,logPowerSeriesEmbedding (v j)*Y j
  map_add' v w := by simp only [Pi.add_apply,map_add,add_mul,Finset.sum_add_distrib]
  map_smul' c v := by
    change (∑ j,logPowerSeriesEmbedding (c • v j)*Y j)=c • (∑ j,logPowerSeriesEmbedding (v j)*Y j)
    rw [logActualScalar_smul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [PowerSeries.smul_eq_C_mul,map_mul]
    have hc : logPowerSeriesEmbedding (PowerSeries.C K c)=Polynomial.C (HahnSeries.C c) := by
      change Polynomial.C (HahnSeries.ofPowerSeries ℤ K (PowerSeries.C K c))=_
      rw [HahnSeries.ofPowerSeries_C]
    rw [hc,mul_assoc]

/-- The actual solution equation intertwines the row connection with twisted
Euler. This is derived from Leibniz, not assumed as a filtered identity. -/
theorem logSolutionRowPairing_intertwines {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (rho : K)
    (Y : Fin r → Polynomial (LaurentSeries K))
    (hY : ∀ i,twistedLogPolynomialEuler rho (Y i)=∑ j,logPowerSeriesEmbedding (C i j)*Y j)
    (v : Fin r → PowerSeries K) :
    literalTwistedEulerLinear rho (logSolutionRowPairing Y v)=
      logSolutionRowPairing Y (powerSeriesEulerRowConnection C v) := by
  change literalTwistedEulerLinear rho (∑ j,logPowerSeriesEmbedding (v j)*Y j)=_
  rw [map_sum]
  simp only [literalTwistedEulerLinear_logfree_mul]
  have hy : ∀ j,literalTwistedEulerLinear rho (Y j)=∑ l,logPowerSeriesEmbedding (C j l)*Y l := hY
  simp only [hy,Finset.sum_add_distrib,Finset.mul_sum]
  change _=∑ j,logPowerSeriesEmbedding (powerSeriesEuler (v j)+∑ l,v l*C l j)*Y j
  simp only [map_add,map_sum,map_mul,add_mul,Finset.sum_mul,Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem logSolutionRowPairing_iterate {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (rho : K)
    (Y : Fin r → Polynomial (LaurentSeries K))
    (hY : ∀ i,twistedLogPolynomialEuler rho (Y i)=∑ j,logPowerSeriesEmbedding (C i j)*Y j)
    (v : Fin r → PowerSeries K) (m : ℕ) :
    (twistedLogPolynomialEuler rho)^[m] (logSolutionRowPairing Y v)=
      logSolutionRowPairing Y ((powerSeriesEulerRowConnection C : _ → _)^[m] v) := by
  induction m with
  | zero =>rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply',ih]
    exact logSolutionRowPairing_intertwines C rho Y hY _

/-- The same polynomial connection matrix used in arithmetic bounds really
acts on every supplied solution. Products of filters are NOT replaced by
pointwise products of their extracted matrices. -/
theorem literalLogPolynomialFilter_solution_identity {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (rho : K)
    (Y : Fin r → Polynomial (LaurentSeries K))
    (hY : ∀ i,twistedLogPolynomialEuler rho (Y i)=∑ j,logPowerSeriesEmbedding (C i j)*Y j)
    (P : Polynomial K) (i : Fin r) :
    literalLogPolynomialFilter rho P (Y i)=
      ∑ j,logPowerSeriesEmbedding (powerSeriesEulerPolynomialConnection C P i j)*Y j := by
  have hv : logSolutionRowPairing Y (fun j =>(1 : Matrix (Fin r) (Fin r) (PowerSeries K)) i j)=Y i := by
    simp [logSolutionRowPairing,Matrix.one_apply]
  have h : literalLogPolynomialFilter rho P
      (logSolutionRowPairing Y (fun j =>(1 : Matrix (Fin r) (Fin r) (PowerSeries K)) i j))=
      logSolutionRowPairing Y (Polynomial.aeval (powerSeriesEulerRowConnection C) P
        (fun j =>(1 : Matrix (Fin r) (Fin r) (PowerSeries K)) i j)) := by
    simp only [literalLogPolynomialFilter,Polynomial.aeval_endomorphism,Polynomial.sum_def,
      LinearMap.sum_apply,Module.End.mul_apply,Polynomial.aeval_C,Module.algebraMap_end_apply,
      Module.End.pow_apply,map_sum,map_smul,logSolutionRowPairing_iterate C rho Y hY]
  rw [hv] at h
  exact h

end StrictEUnit
end
