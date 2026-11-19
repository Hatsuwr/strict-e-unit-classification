import ActualRamifiedTaylor
import GlobalAnalyticLogFrame
import FixedExponentBaseRow

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K I : Type*} [Field K] [CharZero K] [Fintype I] [DecidableEq I]

theorem logRamification_constant_polynomial (N : ℕ) (hN : N ≠ 0)
    (p : Polynomial K) :
    stage38_logRamification N hN (Polynomial.map (algebraMap K (LaurentSeries K)) p) =
      Polynomial.map (algebraMap K (LaurentSeries K)) p := by
  apply Polynomial.ext
  intro i
  simp only [stage38_logRamification_coeff, Polynomial.coeff_map, AlgHom.commutes]

theorem finiteLogMatrixExponential_map_series (J : Matrix I I K)
    (i j : I) :
    laurentLogToSeriesPolynomial (Polynomial.map (algebraMap K (LaurentPolynomial K))
      (finiteLogMatrixExponential J i j)) =
    Polynomial.map (algebraMap K (LaurentSeries K)) (finiteLogMatrixExponential J i j) := by
  apply Polynomial.ext
  intro n
  simp only [laurentLogToSeriesPolynomial, Polynomial.mapRingHom, RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk, Polynomial.coeff_map]
  change laurentPolynomialToSeries (algebraMap K (LaurentPolynomial K)
    ((finiteLogMatrixExponential J i j).coeff n)) = _
  exact laurentPolynomialToSeries.commutes _

theorem fixedExponentBaseUnit_series_row (N : ℕ) (hN : N ≠ 0)
    (F : I → Polynomial (LaurentSeries K)) (p : Polynomial (LaurentSeries K))
    (m : ℤ) (J : Matrix I I K) (hJ : IsNilpotent J) (j : I)
    (hp : p = ∑ i, F i * Polynomial.map (algebraMap K (LaurentSeries K))
      (finiteLogMatrixExponential J i j)) :
    Polynomial.C (HahnSeries.single m (1 : K)) * stage38_logRamification N hN p =
      ∑ i, stage38_logRamification N hN (F i) *
        laurentLogToSeriesPolynomial ((fixedExponentBaseUnit m J hJ).val i j) := by
  rw [fixedExponentBaseUnit_row]
  have hm : laurentLogToSeriesPolynomial (Polynomial.C (LaurentPolynomial.T m)) =
      Polynomial.C (HahnSeries.single m (1 : K)) := by
    change Polynomial.map laurentPolynomialToSeries.toRingHom
      (Polynomial.C (LaurentPolynomial.T m)) = _
    rw [Polynomial.map_C]
    congr 1
    exact laurentPolynomialToSeries_single m (1 : K)
  rw [hm, hp, map_sum]
  simp_rw [map_mul, logRamification_constant_polynomial,
    finiteLogMatrixExponential_map_series]

variable (k : Subfield ℂ)
theorem ramified_analytic_log_image (N : ℕ) (hN : N ≠ 0)
    (F : subfieldEntireFunctionAlgebra k) :
    stage38_logRamification N hN
      (Polynomial.C (stage14_subfieldEntireLaurentAlgHom k F)) =
    Polynomial.C (stage14_subfieldEntireLaurentAlgHom k
      (stage17_arithmeticPowerPullback k N hN F)) := by
  rw [actual_entireLaurent_powerPullback]
  change Polynomial.map (stage38_laurentRamification N hN).toRingHom
    (Polynomial.C (stage14_subfieldEntireLaurentAlgHom k F)) = _
  rw [Polynomial.map_C]
  rfl
end StrictEUnit
end
