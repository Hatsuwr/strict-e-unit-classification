import OrdinaryPointRationalEmbedding
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Roots

/-! Actual power-series regularity of translated rational functions whose
supplied polynomial denominator does not vanish at the chosen point. -/
noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K]

/-- A translated POLYNOMIAL regarded as a power series. -/
def ordinaryPointPolynomialSeries (β : K) (p : Polynomial K) : PowerSeries K :=
  (ordinaryPointPolynomialShift β p : PowerSeries K)

@[simp] theorem ordinaryPointPolynomialSeries_coe (β : K) (p : Polynomial K) :
    HahnSeries.ofPowerSeries ℤ K (ordinaryPointPolynomialSeries β p) =
      ordinaryPointPolynomialMap β p := rfl

@[simp] theorem ordinaryPointPolynomialSeries_constantCoeff (β : K) (p : Polynomial K) :
    PowerSeries.constantCoeff K (ordinaryPointPolynomialSeries β p) = p.eval β := by
  change PowerSeries.constantCoeff K
    ((ordinaryPointPolynomialShift β p : Polynomial K) : PowerSeries K) = _
  rw [Polynomial.constantCoeff_coe, ordinaryPointPolynomialShift_apply,
    Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp]
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, zero_add]

/-- Regularity is derived by constructing the formal inverse of the translated
denominator. No regularity or power-series preimage is supplied. -/
theorem ordinaryPointRationalMap_quotient_regular (β : K) (P T : Polynomial K)
    (hβ : T.eval β ≠ 0) :
    ordinaryPointRationalMap β
      (algebraMap (Polynomial K) (RatFunc K) P /
        algebraMap (Polynomial K) (RatFunc K) T) =
      HahnSeries.ofPowerSeries ℤ K
        (ordinaryPointPolynomialSeries β P * (ordinaryPointPolynomialSeries β T)⁻¹) := by
  have hT : T ≠ 0 := by
    intro h
    apply hβ
    rw [h, Polynomial.eval_zero]
  have ht : ordinaryPointPolynomialMap β T ≠ 0 := by
    intro h
    apply hT
    exact (ordinaryPointPolynomialMap_injective β) (h.trans (map_zero (ordinaryPointPolynomialMap β)).symm)
  have hc : PowerSeries.constantCoeff K (ordinaryPointPolynomialSeries β T) ≠ 0 := by
    rw [ordinaryPointPolynomialSeries_constantCoeff]
    exact hβ
  rw [map_div₀, ordinaryPointRationalMap_polynomial, ordinaryPointRationalMap_polynomial]
  symm
  apply (eq_div_iff ht).mpr
  change HahnSeries.ofPowerSeries ℤ K
      (ordinaryPointPolynomialSeries β P * (ordinaryPointPolynomialSeries β T)⁻¹) *
        HahnSeries.ofPowerSeries ℤ K (ordinaryPointPolynomialSeries β T) =
      HahnSeries.ofPowerSeries ℤ K (ordinaryPointPolynomialSeries β P)
  rw [← map_mul, mul_assoc, PowerSeries.inv_mul_cancel _ hc, mul_one]

/-- An arbitrary rational function with the SAME clearing identity becomes
this explicit power series at every point avoiding its supplied denominator. -/
theorem ordinaryPointRationalMap_of_clearing (β : K) (q : RatFunc K)
    (T U : Polynomial K) (hβ : T.eval β ≠ 0)
    (hclear : algebraMap (Polynomial K) (RatFunc K) U =
      algebraMap (Polynomial K) (RatFunc K) T * q) :
    ordinaryPointRationalMap β q = HahnSeries.ofPowerSeries ℤ K
      (ordinaryPointPolynomialSeries β U * (ordinaryPointPolynomialSeries β T)⁻¹) := by
  have hT : T ≠ 0 := by
    intro h
    apply hβ
    rw [h, Polynomial.eval_zero]
  have heq : q = algebraMap (Polynomial K) (RatFunc K) U /
      algebraMap (Polynomial K) (RatFunc K) T := by
    apply (eq_div_iff (RatFunc.algebraMap_ne_zero hT)).mpr
    rw [hclear, mul_comm]
  rw [heq]
  exact ordinaryPointRationalMap_quotient_regular β U T hβ

/-- A nonzero polynomial has an ordinary point over any infinite field.
Characteristic zero is sufficient, but is not needed in this scalar lemma. -/
theorem exists_ordinaryPoint_avoiding (T : Polynomial K) (hT : T ≠ 0)
    [Infinite K] : ∃ β : K, T.eval β ≠ 0 := by
  classical
  by_contra h
  apply hT
  apply Polynomial.zero_of_eval_zero
  intro β
  by_contra hβ
  exact h ⟨β, hβ⟩

end StrictEUnit
end
