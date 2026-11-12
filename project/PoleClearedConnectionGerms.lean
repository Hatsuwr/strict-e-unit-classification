import PowerSeriesInverseIntegralPowers
import SelectedDifferentialShearData
import ActualMinimalPolynomialConnection

/-! Exact full source connection germs at the original center, including a
singular center. Only the literal pole power is removed; the original T is
retained in the clearing and rational-connection identities. -/
noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

def poleClearedPolynomialQuotientGerm (T P : Polynomial K) (m : ℕ) : PowerSeries K :=
  (P : PowerSeries K)*((sameCompanionEulerDenominatorSeries T)⁻¹)^m

def samePoleClearedDividedConnectionGerm {r : ℕ} (T : Polynomial K)
    (U : Matrix (Fin r) (Fin r) (Polynomial K)) (m : ℕ) :
    Matrix (Fin r) (Fin r) (PowerSeries K) :=
  fun i j => poleClearedPolynomialQuotientGerm T
    (dividedPolynomialConnectionSequence T U m i j) m

theorem poleClearedPolynomialQuotientGerm_clearing
    (T P : Polynomial K) (hT : T≠0) (m : ℕ) :
    (T : PowerSeries K)^m*poleClearedPolynomialQuotientGerm T P m=
      (PowerSeries.X : PowerSeries K)^(T.natTrailingDegree*m)*(P : PowerSeries K) := by
  let f := sameCompanionEulerDenominatorSeries T
  have hi : f*f⁻¹=1 := PowerSeries.mul_inv_cancel f
    (sameCompanionEulerDenominatorSeries_constantCoeff_ne_zero T hT)
  rw [← sameCompanionEulerDenominatorSeries_factor T,mul_pow]
  change ((PowerSeries.X : PowerSeries K)^T.natTrailingDegree)^m*f^m*
    ((P : PowerSeries K)*(f⁻¹)^m)=_
  calc
    _ = ((PowerSeries.X : PowerSeries K)^T.natTrailingDegree)^m*(P : PowerSeries K)*
        (f^m*(f⁻¹)^m) := by ring
    _ = _ := by rw [← mul_pow,hi,one_pow,mul_one,← pow_mul]

theorem samePoleClearedDividedConnectionGerm_clearing {r : ℕ}
    (T : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K)) (hT : T≠0)
    (m : ℕ) (i j : Fin r) :
    (T : PowerSeries K)^m*samePoleClearedDividedConnectionGerm T U m i j=
      (PowerSeries.X : PowerSeries K)^(T.natTrailingDegree*m)*
        (dividedPolynomialConnectionSequence T U m i j : PowerSeries K) :=
  poleClearedPolynomialQuotientGerm_clearing T _ hT m

/-- These germs are the original rational higher-derivative matrices divided
by m!, times exactly the restored coordinate pole power. No new connection
or solution-family identification is supplied. -/
theorem samePoleClearedDividedConnectionGerm_rational_identity {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (RatFunc K))
    (T : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K)) (hT : T≠0)
    (hclear : ∀ i j,algebraMap (Polynomial K) (RatFunc K) (U i j)=
      algebraMap (Polynomial K) (RatFunc K) T*A i j)
    (m : ℕ) (i j : Fin r) :
    HahnSeries.ofPowerSeries ℤ K (samePoleClearedDividedConnectionGerm T U m i j)=
      (HahnSeries.ofPowerSeries ℤ K PowerSeries.X)^(T.natTrailingDegree*m)*
        algebraMap (RatFunc K) (LaurentSeries K)
          ((m.factorial : RatFunc K)⁻¹*matrixConnectionSequence
            stage14_rationalOrdinaryDerivation A m i j) := by
  let psi : PowerSeries K →+* LaurentSeries K := HahnSeries.ofPowerSeries ℤ K
  have ht : psi (T : PowerSeries K)≠0 := polynomialLaurentImage_ne_zero T hT
  have h := congrArg (algebraMap (RatFunc K) (LaurentSeries K))
    ((stage14_polynomial_connection_maps A T U hclear).2 m i j)
  simp only [map_mul,map_inv₀,map_natCast,map_pow,
    ← IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) (LaurentSeries K),
    Polynomial.algebraMap_hahnSeries_apply] at h
  have hc := congrArg psi (samePoleClearedDividedConnectionGerm_clearing T U hT m i j)
  simp only [map_mul,map_pow] at hc
  apply mul_right_cancel₀ (pow_ne_zero m ht)
  change psi (samePoleClearedDividedConnectionGerm T U m i j)*(psi (T : PowerSeries K))^m=_
  calc
    _ = (psi PowerSeries.X)^(T.natTrailingDegree*m)*
        psi (dividedPolynomialConnectionSequence T U m i j : PowerSeries K) :=
      (mul_comm _ _).trans hc
    _ = _ := by
      rw [h]
      simp only [map_mul,map_inv₀,map_natCast]
      ring

end StrictEUnit
end
