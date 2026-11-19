import PoleClearedConnectionArithmetic

/-! Restore the exact source poles without losing exponential common
arithmetic. Every Laurent coefficient up to the cutoff is covered, including
negative indices, jointly with all divided derivative orders up to it. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K]

theorem powerSeries_monomial_laurent_coefficient (f : PowerSeries K)
    (x : LaurentSeries K) (a : ℕ)
    (h : HahnSeries.ofPowerSeries ℤ K f=
      (HahnSeries.ofPowerSeries ℤ K PowerSeries.X)^a*x) (k : ℤ) :
    x.coeff k=if hk : 0≤(a : ℤ)+k then
      PowerSeries.coeff K (((a : ℤ)+k).toNat) f else 0 := by
  have he := congrArg (fun y : LaurentSeries K => y.coeff (k+(a : ℤ))) h
  dsimp only at he
  rw [← map_pow,HahnSeries.ofPowerSeries_X_pow,HahnSeries.coeff_single_mul_add,one_mul] at he
  rw [add_comm k (a : ℤ)] at he
  by_cases hk : 0≤(a : ℤ)+k
  · rw [dif_pos hk]
    have hn : (a : ℤ)+k=((((a : ℤ)+k).toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg hk).symm
    rw [hn,HahnSeries.ofPowerSeries_apply_coeff] at he
    exact he.symm
  · rw [dif_neg hk]
    rw [powerSeries_laurent_coeff_neg _ _ (by omega)] at he
    exact he.symm

theorem bivariate_germ_denominators_laurent_prefix {ι : Type*}
    (g : ℕ → ι → PowerSeries K) (x : ℕ → ι → LaurentSeries K) (t : ℕ)
    (hidentity : ∀ m i,HahnSeries.ofPowerSeries ℤ K (g m i)=
      (HahnSeries.ofPowerSeries ℤ K PowerSeries.X)^(t*m)*x m i)
    (C : ℝ) (hC : 1≤C)
    (hden : ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D : ℝ)≤C^(N+1) ∧
      ∀ m l,m+l≤N → ∀ i,IsIntegral ℤ ((D : K)*PowerSeries.coeff K l (g m i))) :
    1≤C^(t+2) ∧ ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D : ℝ)≤(C^(t+2))^(N+1) ∧
      ∀ m,m≤N → ∀ k : ℤ,k≤(N : ℤ) → ∀ i,IsIntegral ℤ ((D : K)*(x m i).coeff k) := by
  refine ⟨one_le_pow₀ hC,?_⟩
  intro N
  obtain ⟨D,hD,hDb,hDi⟩ := hden ((t+2)*N)
  refine ⟨D,hD,?_,?_⟩
  · apply hDb.trans
    rw [← pow_mul]
    apply pow_le_pow_right₀ hC
    simp only [Nat.mul_add,Nat.mul_one]
    omega
  · intro m hm k hk i
    rw [powerSeries_monomial_laurent_coefficient (g m i) (x m i) (t*m) (hidentity m i) k]
    split_ifs with hnonneg
    · have hl : (((t*m : ℕ) : ℤ)+k).toNat≤t*m+N := by
        have hh : ((t*m : ℕ) : ℤ)+k≤((t*m+N : ℕ) : ℤ) := by exact_mod_cast (add_le_add_left hk ((t*m : ℕ) : ℤ))
        simpa only [Int.toNat_natCast] using Int.toNat_le_toNat hh
      have hmul : t*m≤t*N := Nat.mul_le_mul_left t hm
      apply hDi m _
      calc
        m+(((t*m : ℕ) : ℤ)+k).toNat≤N+(t*N+N) := by omega
        _ = (t+2)*N := by ring
    · rw [mul_zero]
      exact isIntegral_zero

end StrictEUnit
end
