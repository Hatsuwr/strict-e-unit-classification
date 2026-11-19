import SelectedEulerPowerSeriesCoefficients
import Mathlib.Algebra.Polynomial.Inductions

noncomputable section
namespace StrictEUnit

/-- A literal finite polynomial realizing the existing coefficient tail. -/
def polynomialTailPolynomial {K : Type*} [Semiring K]
    (d : ℕ) (P : Polynomial K) : Polynomial K :=
  (Polynomial.divX^[d]) P

theorem polynomialTailPolynomial_coeff {K : Type*} [Semiring K]
    (P : Polynomial K) (d k : ℕ) :
    (polynomialTailPolynomial d P).coeff k=P.coeff (k+d) := by
  unfold polynomialTailPolynomial
  induction d generalizing k with
  | zero => rfl
  | succ d ih =>
    rw [Function.iterate_succ_apply',Polynomial.coeff_divX,ih]
    congr 1
    omega

/-- Exact equality, including order zero and tails beyond the degree. -/
theorem polynomialTailPolynomial_coe {K : Type*} [CommSemiring K]
    (d : ℕ) (P : Polynomial K) :
    (polynomialTailPolynomial d P:PowerSeries K)=polynomialTailPowerSeries d P := by
  ext k
  simp only [Polynomial.coeff_coe,polynomialTailPolynomial_coeff,
    polynomialTailPowerSeries,PowerSeries.coeff_mk]

theorem polynomialTailPolynomial_map {K L : Type*} [Semiring K] [Semiring L]
    (φ : K →+* L) (d : ℕ) (P : Polynomial K) :
    (polynomialTailPolynomial d P).map φ=polynomialTailPolynomial d (P.map φ) := by
  ext k
  simp only [Polynomial.coeff_map,polynomialTailPolynomial_coeff]

/-- Coefficient maps preserve the literal tail without changing its index. -/
theorem polynomialTailPowerSeries_map {K L : Type*} [CommSemiring K] [CommSemiring L]
    (φ : K →+* L) (d : ℕ) (P : Polynomial K) :
    PowerSeries.map φ (polynomialTailPowerSeries d P)=
      (((polynomialTailPolynomial d P).map φ):PowerSeries L) := by
  ext k
  simp only [PowerSeries.coeff_map,polynomialTailPowerSeries,PowerSeries.coeff_mk,
    Polynomial.coeff_coe,Polynomial.coeff_map,polynomialTailPolynomial_coeff]

/-- This is inverse uniqueness for a genuine unit power series; no field
structure on the power-series ring is assumed. -/
theorem powerSeries_map_inv_of_constantCoeff_ne_zero
    {K L : Type*} [Field K] [Field L] (φ : K →+* L) (P : PowerSeries K)
    (hP : PowerSeries.constantCoeff K P ≠ 0) :
    PowerSeries.map φ P⁻¹=(PowerSeries.map φ P)⁻¹ := by
  have hm : PowerSeries.constantCoeff L (PowerSeries.map φ P) ≠ 0 := by
    simpa only [← PowerSeries.coeff_zero_eq_constantCoeff,PowerSeries.coeff_map] using
      (map_ne_zero φ).2 hP
  have hne : PowerSeries.map φ P ≠ 0 := by
    intro hz
    exact hm (by rw [hz,map_zero])
  apply mul_left_cancel₀ hne
  have hi := congrArg (PowerSeries.map φ) (PowerSeries.mul_inv_cancel P hP)
  rw [map_mul,map_one] at hi
  exact hi.trans (PowerSeries.mul_inv_cancel (PowerSeries.map φ P) hm).symm

end StrictEUnit
end
