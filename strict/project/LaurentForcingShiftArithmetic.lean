import FiniteForcingArithmeticClosure

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Fixed integer shifts, including negative ones, preserve Laurent forcing
arithmetic. The input cutoff grows additively, never factorially. -/
theorem laurentForcingArithmetic_integer_shift {r : ℕ}
    (b : Fin r →LaurentSeries K) (hb : LaurentForcingArithmetic b) (k : ℤ) :
    LaurentForcingArithmetic (fun i =>HahnSeries.single k (1:K)*b i) := by
  obtain ⟨W,C,hC,hlow,hden⟩ := hb
  have hk : -(k.natAbs:ℤ)≤k := by
    rw [Int.natCast_natAbs]
    exact neg_abs_le k
  have hc (i : Fin r) (l : ℤ) :
      (HahnSeries.single k (1:K)*b i).coeff l=(b i).coeff (l-k) := by
    have he : l=(l-k)+k := by omega
    conv_lhs => rw [he]
    rw [HahnSeries.coeff_single_mul_add,one_mul]
  refine ⟨W+k.natAbs,C^(k.natAbs+2),one_le_pow₀ hC,?_,?_⟩
  · intro i l hl
    rw [hc]
    apply hlow
    simp only [Nat.cast_add] at hl
    omega
  · intro N
    obtain ⟨D,hD,hDb,hDi⟩ := hden (N+k.natAbs)
    refine ⟨D,hD,?_,?_⟩
    · apply hDb.trans
      rw [← pow_mul]
      apply pow_le_pow_right₀ hC
      simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one]
      omega
    · intro i l hl
      rw [hc]
      apply hDi
      simp only [Nat.cast_add]
      omega

end StrictEUnit
end
