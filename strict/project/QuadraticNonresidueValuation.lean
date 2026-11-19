import ArithmeticProgressionPrimeObstruction

noncomputable section
namespace StrictEUnit
variable {K Γ₀ : Type*} [Field K] [CharZero K] [LinearOrderedCommGroupWithZero Γ₀]

theorem valuation_intCast_unit_of_not_dvd (v : Valuation K Γ₀)
    (p : ℕ) (hp : p.Prime) (hvp : v (p : K) < 1)
    (z : ℤ) (hz : ¬ (p : ℤ) ∣ z) : v (z : K) = 1 := by
  have h := valuation_coprime_nat_eq_one v p z.natAbs hvp
    (hp.coprime_iff_not_dvd.mpr (fun hd => hz (Int.natCast_dvd.mpr hd)))
  rcases Int.natAbs_eq z with he | he
  · have he' : (z : K) = (z.natAbs : K) := by simpa only [Int.cast_natCast, Int.cast_neg] using congrArg (fun z : ℤ => (z : K)) he
    rw [he']; exact h
  · have he' : (z : K) = -(z.natAbs : K) := by simpa only [Int.cast_natCast, Int.cast_neg] using congrArg (fun z : ℤ => (z : K)) he
    rw [he', v.map_neg]; exact h

/-- A nonsquare residue of the actual quadratic equation supplies every
translate-unit certificate at any p-place. No residue-field extension is assumed. -/
theorem quadratic_nonresidue_translate_unit (v : Valuation K Γ₀)
    (p : ℕ) (hp : p.Prime) (hvp : v (p : K) < 1)
    (a : K) (d : ℤ) (ha : a^2 = (d : K))
    (hnr : ∀ x : ZMod p, x^2 ≠ (d : ZMod p)) :
    ∀ j : ℕ, v (a - (j : K)) = 1 := by
  have ha1 : v a ≤ 1 := by
    have hs : (v a)^2 ≤ 1 := by rw [← map_pow, ha]; exact valuation_intCast_le_one v d
    by_contra h
    exact (not_lt_of_ge hs) (one_lt_pow₀ (lt_of_not_ge h) (by decide : 2 ≠ 0))
  intro j
  have hj := valuation_natCast_le_one v j
  have hsub := v.map_sub_le ha1 hj
  apply le_antisymm hsub
  by_contra h
  have hlt : v (a - (j : K)) < 1 := lt_of_not_ge h
  have hadd : v (a + (j : K)) ≤ 1 := (v.map_add _ _).trans (max_le ha1 hj)
  have hprod : v ((a - (j : K)) * (a + (j : K))) < 1 := by
    rw [map_mul]
    exact (mul_le_mul_left' hadd _).trans_lt (by simpa using hlt)
  have hid : (a - (j : K)) * (a + (j : K)) = ((d - (j : ℤ)^2 : ℤ) : K) := by
    push_cast
    linear_combination ha
  have hnd : ¬ (p : ℤ) ∣ d - (j : ℤ)^2 := by
    intro hd
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (d - (j : ℤ)^2) p).mpr hd
    push_cast at hz
    exact hnr (j : ZMod p) (sub_eq_zero.mp hz).symm
  rw [hid, valuation_intCast_unit_of_not_dvd v p hp hvp _ hnd] at hprod
  exact lt_irrefl _ hprod

end StrictEUnit
end
