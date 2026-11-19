import LaurentOrdinaryDerivation

/-! The kernel of the ACTUAL ordinary Laurent derivative in characteristic
zero is exactly the literal constant embedding. No analytic premise is used. -/
noncomputable section
namespace StrictEUnit

/-- Every nonzero Laurent exponent vanishes in an ordinary-derivative
constant; its constant is exactly its coefficient at exponent zero. -/
theorem laurentOrdinaryDerivation_eq_zero_iff_eq_constant
    {K : Type*} [Field K] [CharZero K] (f : LaurentSeries K) :
    laurentOrdinaryDerivation f = 0 ↔
      f = algebraMap K (LaurentSeries K) (f.coeff 0) := by
  constructor
  · intro hf
    ext n
    rw [LaurentSeries.algebraMap_apply, HahnSeries.C_apply]
    by_cases hn : n = 0
    · subst n
      rw [HahnSeries.coeff_single_same]
    · rw [HahnSeries.coeff_single_of_ne hn]
      have hc := congrArg (fun g : LaurentSeries K => g.coeff (n-1)) hf
      dsimp only at hc
      simp only [laurentOrdinaryDerivation_coeff, sub_add_cancel,
        HahnSeries.coeff_zero] at hc
      exact (mul_eq_zero.mp hc).resolve_left (Int.cast_ne_zero.mpr hn)
  · intro hf
    rw [hf]
    exact (laurentOrdinaryDerivation (k := K)).map_algebraMap _

/-- Exact constant-field statement for the actual ordinary Laurent derivative. -/
theorem laurentOrdinaryDerivation_eq_zero_iff_exists_constant
    {K : Type*} [Field K] [CharZero K] (f : LaurentSeries K) :
    laurentOrdinaryDerivation f = 0 ↔
      ∃ c : K, f = algebraMap K (LaurentSeries K) c := by
  constructor
  · intro hf
    exact ⟨f.coeff 0,
      (laurentOrdinaryDerivation_eq_zero_iff_eq_constant f).mp hf⟩
  · rintro ⟨c, rfl⟩
    exact (laurentOrdinaryDerivation (k := K)).map_algebraMap c

end StrictEUnit
end
