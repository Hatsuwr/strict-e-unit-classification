import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-! New reconstruction, not recovered historical source.
The minimal coefficient-extension homomorphism needed for analytic closure.
Its action is literal coefficientwise mapping. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
variable {K L : Type*} [Field K] [Field L]

/-- Literal coefficient extension of Laurent series, bundled as a ring map. -/
def relativeClosureLaurentMap (φ : K →+* L) : LaurentSeries K →+* LaurentSeries L where
  toFun x := x.map φ
  map_one' := HahnSeries.map_one φ.toMonoidWithZeroHom
  map_mul' _ _ := HahnSeries.map_mul φ.toNonUnitalRingHom
  map_zero' := HahnSeries.map_zero φ.toZeroHom
  map_add' _ _ := HahnSeries.map_add φ.toAddMonoidHom

@[simp] theorem relativeClosureLaurentMap_coeff (φ : K →+* L)
    (x : LaurentSeries K) (n : ℤ) :
    (relativeClosureLaurentMap φ x).coeff n = φ (x.coeff n) := rfl

@[simp] theorem relativeClosureLaurentMap_ofPowerSeries (φ : K →+* L)
    (x : PowerSeries K) :
    relativeClosureLaurentMap φ (HahnSeries.ofPowerSeries ℤ K x) =
      HahnSeries.ofPowerSeries ℤ L (PowerSeries.map φ x) := by
  ext n
  change φ (((x : PowerSeries K) : LaurentSeries K).coeff n) =
    ((PowerSeries.map φ x : PowerSeries L) : LaurentSeries L).coeff n
  by_cases hn : n < 0
  · simp only [PowerSeries.coeff_coe, if_pos hn, map_zero]
  · simp only [PowerSeries.coeff_coe, if_neg hn, PowerSeries.coeff_map]

@[simp] theorem relativeClosureLaurentMap_polynomial (φ : K →+* L)
    (p : Polynomial K) :
    relativeClosureLaurentMap φ (algebraMap (Polynomial K) (LaurentSeries K) p) =
      algebraMap (Polynomial L) (LaurentSeries L) (p.map φ) := by
  rw [Polynomial.algebraMap_hahnSeries_apply, relativeClosureLaurentMap_ofPowerSeries,
    Polynomial.algebraMap_hahnSeries_apply, Polynomial.polynomial_map_coe]

theorem relativeClosureLaurentMap_comp_polynomial (φ : K →+* L) :
    (algebraMap (Polynomial L) (LaurentSeries L)).comp (Polynomial.mapRingHom φ) =
      (relativeClosureLaurentMap φ).comp
        (algebraMap (Polynomial K) (LaurentSeries K)) := by
  apply RingHom.ext
  intro p
  exact (relativeClosureLaurentMap_polynomial φ p).symm

/-- Polynomial integrality is preserved by coefficient extension. -/
theorem relativeClosureLaurentMap_isIntegral (φ : K →+* L)
    {x : LaurentSeries K} (hx : IsIntegral (Polynomial K) x) :
    IsIntegral (Polynomial L) (relativeClosureLaurentMap φ x) :=
  hx.map_of_comp_eq (Polynomial.mapRingHom φ) (relativeClosureLaurentMap φ)
    (relativeClosureLaurentMap_comp_polynomial φ)

end StrictEUnit
