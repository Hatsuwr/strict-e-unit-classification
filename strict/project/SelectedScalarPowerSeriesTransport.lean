import LaurentOrdinaryDerivation

/-! Transport the literal selected tuple through the existing injective
PowerSeries-to-LaurentSeries embedding; no scalar operator is selected here. -/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

theorem powerSeries_equation_of_laurent_scalar_equation
    {K : Type*} [Field K] (G : PowerSeries K) (r : ℕ)
    (q : Fin (r+1) → Polynomial K)
    (hode : (∑ i, algebraMap (Polynomial K) (RatFunc K) (q i) •
      (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val]
        (HahnSeries.ofPowerSeries ℤ K G)) = 0) :
    (∑ i, (q i : PowerSeries K) * (PowerSeries.derivative K)^[i.val] G) = 0 := by
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := K)
  rw [map_sum, map_zero]
  calc
    _ = ∑ i, algebraMap (Polynomial K) (RatFunc K) (q i) •
        (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val]
          (HahnSeries.ofPowerSeries ℤ K G) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_mul, Algebra.smul_def,
        ← IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) (LaurentSeries K),
        Polynomial.algebraMap_hahnSeries_apply,
        laurentOrdinaryDerivation_iterate_ofPowerSeries]
    _ = 0 := hode

end StrictEUnit
end
