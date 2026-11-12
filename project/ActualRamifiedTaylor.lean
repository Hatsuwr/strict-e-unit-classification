import Stage17RamifiedLaurentCoefficients
import Stage38FormalRamification

noncomputable section
namespace StrictEUnit
theorem actual_entireLaurent_powerPullback (k : Subfield ℂ)
    (N : ℕ) (hN : N ≠ 0) (e : subfieldEntireFunctionAlgebra k) :
    stage14_subfieldEntireLaurentAlgHom k (stage17_arithmeticPowerPullback k N hN e) =
      stage38_laurentRamification N hN (stage14_subfieldEntireLaurentAlgHom k e) := by
  apply HahnSeries.ext
  funext n
  by_cases hn : n ∈ Set.range (stage38_exponentScale N)
  · obtain ⟨a, rfl⟩ := hn
    change (HahnSeries.ofPowerSeries ℤ k
      (subfieldEntireTaylorAlgHom k (stage17_arithmeticPowerPullback k N hN e))).coeff
        ((N : ℤ) * a) =
      (stage38_laurentRamification N hN (stage14_subfieldEntireLaurentAlgHom k e)).coeff
        ((N : ℤ) * a)
    rw [stage38_laurentRamification_coeff]
    by_cases ha : 0 ≤ a
    · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le ha
      rw [← Nat.cast_mul, HahnSeries.ofPowerSeries_apply_coeff,
        stage14_subfieldEntireLaurentAlgHom_apply, HahnSeries.ofPowerSeries_apply_coeff]
      apply Subtype.ext
      simpa [subfieldEntireTaylorAlgHom, subfieldEntireTaylorSeries,
        Nat.mul_div_right _ (Nat.pos_of_ne_zero hN)] using
        stage17_entirePowerPullback_coefficient N hN e.val (N * j)
    · rw [powerSeries_laurent_coeff_neg _ _ (mul_neg_of_pos_of_neg
        (by exact_mod_cast Nat.pos_of_ne_zero hN) (lt_of_not_ge ha)),
        stage14_subfieldEntireLaurentAlgHom_apply,
        powerSeries_laurent_coeff_neg _ a (lt_of_not_ge ha)]
  · rw [stage38_laurentRamification_coeff_outside N hN _ n hn,
      stage14_subfieldEntireLaurentAlgHom_apply]
    by_cases hpos : 0 ≤ n
    · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hpos
      rw [HahnSeries.ofPowerSeries_apply_coeff]
      apply Subtype.ext
      have hdiv : ¬ N ∣ j := by
        rintro ⟨a, rfl⟩
        apply hn
        refine ⟨(a : ℤ), ?_⟩
        simp [stage38_exponentScale]
      simpa [subfieldEntireTaylorAlgHom, subfieldEntireTaylorSeries, hdiv] using
        stage17_entirePowerPullback_coefficient N hN e.val j
    · exact powerSeries_laurent_coeff_neg _ n (lt_of_not_ge hpos)

end StrictEUnit
