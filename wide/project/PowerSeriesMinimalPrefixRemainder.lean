import MinimalPrefixRemainder

/-! NEW SOURCE-ONLY, UNCOMPILED. Nonvanishing for precisely the independent
PowerSeries derivative prefix. No unit channel, next derivative, contact,
rank, covariant-row, or Galochkin claim is added. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit

/-- A nonzero polynomial row on a rationally independent embedded family
has a nonzero literal PowerSeries remainder. -/
theorem powerSeries_polynomial_row_remainder_ne_zero {K : Type*} [Field K]
    {r : ℕ} (U : Fin r → PowerSeries K)
    (hU : LinearIndependent (RatFunc K)
      (fun i => HahnSeries.ofPowerSeries ℤ K (U i)))
    (P : Fin r → Polynomial K) (hP : ∃ i, P i ≠ 0) :
    (∑ i, (P i : PowerSeries K) * U i) ≠ 0 := by
  intro hz
  apply polynomial_row_remainder_ne_zero
    (fun i => HahnSeries.ofPowerSeries ℤ K (U i)) hU P hP
  calc
    _ = HahnSeries.ofPowerSeries ℤ K (∑ i, (P i : PowerSeries K) * U i) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Polynomial.algebraMap_hahnSeries_apply, map_mul]
    _ = 0 := by rw [hz, map_zero]

/-- Apply the bridge to the exact derivative prefix encoded by the accepted
minimal cyclic data for the literal embedding of G. In the original-input
application G is mk(ordinaryBorelFieldCoefficient F a hmem), unchanged. -/
theorem powerSeries_minimal_prefix_remainder_ne_zero {K : Type*} [Field K]
    (G : PowerSeries K) (r : ℕ) (b : Fin r → RatFunc K)
    (hdata : OrdinaryBorelMinimalCyclicData (HahnSeries.ofPowerSeries ℤ K G) r b)
    (P : Fin r → Polynomial K) (hP : ∃ i, P i ≠ 0) :
    (∑ i, (P i : PowerSeries K) *
      (PowerSeries.derivative K)^[i.val] G) ≠ 0 := by
  apply powerSeries_polynomial_row_remainder_ne_zero
    (fun i : Fin r => (PowerSeries.derivative K)^[i.val] G) ?_ P hP
  have hli := hdata.1
  simpa only [laurentOrdinaryDerivation_iterate_ofPowerSeries] using hli

end StrictEUnit
end
