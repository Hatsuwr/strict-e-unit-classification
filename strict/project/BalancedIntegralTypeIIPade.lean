import IntegralTypeIIPade

/-! SOURCE-ONLY. Uniform Type-II House bounds for the exact same finite-family
arithmetic certificate. No rank theorem or connection denominator estimate. -/
noncomputable section
open scoped BigOperators Classical NumberField
namespace StrictEUnit

def typeIIExponentialBase (κ C : ℝ) (r : ℕ) : ℝ :=
  4 * max 1 (max 1 (κ^2) * ((2*r : ℕ) : ℝ)^2) * C^(4*(2*r+1))

/-- Exact exponent one, with no positivity assumption on the Siegel constant. -/
theorem typeII_balanced_kernel_bound (κ H : ℝ) (r t : ℕ)
    (hr : 0 < r) (ht : 0 < t) :
    max 1 (κ * ((κ * ((2*r*t-1 : ℕ) + 1) * H) ^
      (((r*t : ℕ) : ℝ) / (((2*r*t-1 : ℕ)+1) - (r*t : ℕ) : ℝ)))) =
      max 1 (κ^2 * ((2*r*t : ℕ) : ℝ) * H) := by
  have hrt : 0 < r*t := Nat.mul_pos hr ht
  have hdim : 2*r*t-1+1 = 2*r*t :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.mul_pos (Nat.mul_pos (by decide : 0 < 2) hr) ht))
  have hden : (((2*r*t : ℕ) : ℝ) - ((r*t : ℕ) : ℝ)) = ((r*t : ℕ) : ℝ) := by
    push_cast
    ring
  have hne : ((r*t : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hrt)
  rw [show ((2*r*t-1 : ℕ) : ℝ)+1 = ((2*r*t : ℕ) : ℝ) by exact_mod_cast hdim,
    hden, div_self hne, Real.rpow_one]
  congr 1
  ring

/-- Both the denominator and numerator bounds are absorbed by one fixed base. -/
theorem typeII_balanced_house_exponential (κ C : ℝ) (r : ℕ)
    (hC : 1 ≤ C) (hr : 0 < r) :
    1 ≤ typeIIExponentialBase κ C r ∧
    ∀ t : ℕ, 0 < t →
      let H := C^((2*(2*r+1))*t)
      let E := max 1 (κ^2 * ((2*r*t : ℕ) : ℝ) * H)
      H*E ≤ (typeIIExponentialBase κ C r)^t ∧
      ((2*r*t : ℕ) : ℝ)*H*E ≤ (typeIIExponentialBase κ C r)^t := by
  let A := max 1 (κ^2)
  let J := max 1 (A * ((2*r : ℕ) : ℝ)^2)
  have hA : 1 ≤ A := le_max_left _ _
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hJ : 1 ≤ J := le_max_left _ _
  have hJ0 : 0 ≤ J := zero_le_one.trans hJ
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  constructor
  · exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by norm_num) hJ) (one_le_pow₀ hC)
  · intro t ht
    dsimp only
    let H := C^((2*(2*r+1))*t)
    let c : ℝ := ((2*r*t : ℕ) : ℝ)
    have hc : 1 ≤ c := by
      change (1 : ℝ) ≤ ((2*r*t : ℕ) : ℝ)
      exact_mod_cast (Nat.succ_le_of_lt (Nat.mul_pos (Nat.mul_pos (by decide : 0 < 2) hr) ht))
    have hc0 : 0 ≤ c := zero_le_one.trans hc
    have hH : 1 ≤ H := one_le_pow₀ hC
    have hH0 : 0 ≤ H := zero_le_one.trans hH
    have hE : max 1 (κ^2*c*H) ≤ A*c*H := by
      apply max_le
      · exact one_le_mul_of_one_le_of_one_le
          (one_le_mul_of_one_le_of_one_le hA hc) hH
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right 1 (κ^2)) hc0) hH0
    have hnat : (t : ℝ) ≤ (2 : ℝ)^t := by
      exact_mod_cast (Nat.le_of_lt t.lt_two_pow_self)
    have hsq : (t : ℝ)^2 ≤ (4 : ℝ)^t := by
      calc
        _ ≤ ((2 : ℝ)^t)^2 := pow_le_pow_left₀ (Nat.cast_nonneg t) hnat 2
        _ = ((2 : ℝ)^2)^t := by rw [← pow_mul, ← pow_mul, Nat.mul_comm t 2]
        _ = _ := by norm_num
    have hconst : A*((2*r : ℕ) : ℝ)^2 ≤ J^t :=
      (le_max_right _ _).trans (le_self_pow₀ hJ (Nat.ne_of_gt ht))
    have hmain : c*H*max 1 (κ^2*c*H) ≤ (typeIIExponentialBase κ C r)^t := by
      calc
        _ ≤ c*H*(A*c*H) := mul_le_mul_of_nonneg_left hE (mul_nonneg hc0 hH0)
        _ = (A*((2*r : ℕ) : ℝ)^2)*(t : ℝ)^2*C^((4*(2*r+1))*t) := by
          dsimp only [c, H]
          rw [show C^((4*(2*r+1))*t) = (C^((2*(2*r+1))*t))^2 by
            rw [← pow_mul]; congr 1; ring]
          simp only [Nat.cast_mul, Nat.cast_ofNat]
          ring
        _ ≤ (J^t*(4 : ℝ)^t)*C^((4*(2*r+1))*t) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hconst hsq (sq_nonneg _) (pow_nonneg hJ0 t)) (pow_nonneg hC0 _)
        _ = (typeIIExponentialBase κ C r)^t := by
          simp only [typeIIExponentialBase, J, A, mul_pow, ← pow_mul]
          ring
    refine ⟨?_, hmain⟩
    exact (mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_left hH0 hc) (zero_le_one.trans (le_max_left _ _))).trans hmain

/-- Same f, same delta and same integral prefix b throughout. Each parameter
constructs new Q/P; no supplied approximants, unit coefficient or rank premise. -/
theorem exists_exponential_integral_typeII_pade
    (K : Type*) [Field K] [NumberField K]
    (r : ℕ) (hr : 0 < r) (f : Fin r → PowerSeries K)
    (C : ℝ) (hC : 1 ≤ C) (δ : ℕ → ℕ) (hδ : ∀ L, 0 < δ L)
    (hδbound : ∀ L, (δ L : ℝ) ≤ C^(L+1))
    (b : ℕ → Fin r → ℕ → 𝓞 K)
    (hb : ∀ L j n, n ≤ L → (b L j n : K) = (δ L : K)*PowerSeries.coeff K n (f j))
    (hhouse : ∀ L j n, n ≤ L → NumberField.house (b L j n : K) ≤ C^(2*(L+1))) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ t : ℕ, 0 < t →
      ∃ Q : Polynomial (𝓞 K), ∃ P : Fin r → Polynomial (𝓞 K),
        Q ≠ 0 ∧ Q.natDegree ≤ 2*r*t-1 ∧ (∀ j, (P j).natDegree ≤ 2*r*t-1) ∧
        (∀ j, (P j).map (algebraMap (𝓞 K) K) = PowerSeries.trunc (2*r*t)
          ((Q.map (algebraMap (𝓞 K) K) : PowerSeries K)*f j)) ∧
        (∀ j n, n < (2*r+1)*t → PowerSeries.coeff K n
          (((Q.map (algebraMap (𝓞 K) K) : PowerSeries K)*f j) -
            ((P j).map (algebraMap (𝓞 K) K) : PowerSeries K)) = 0) ∧
        (∀ n, NumberField.house (Q.coeff n : K) ≤ B^t) ∧
        (∀ j n, NumberField.house ((P j).coeff n : K) ≤ B^t) := by
  obtain ⟨κ, hκ⟩ := exists_integral_typeII_pade K
  obtain ⟨hB, hbound⟩ := typeII_balanced_house_exponential κ C r hC hr
  refine ⟨typeIIExponentialBase κ C r, hB, ?_⟩
  intro t ht
  let N := 2*r*t-1
  let L := N+t
  have hrt : 0 < r*t := Nat.mul_pos hr ht
  have hdim : N+1 = 2*r*t := by
    dsimp only [N]
    exact Nat.sub_add_cancel
      (Nat.succ_le_of_lt (Nat.mul_pos (Nat.mul_pos (by decide : 0 < 2) hr) ht))
  have hL : L+1 = (2*r+1)*t := by
    calc
      _ = (N+1)+t := by dsimp only [L]; omega
      _ = _ := by rw [hdim]; ring
  have hsize : r*t < N+1 := by rw [hdim]; nlinarith
  have hδH : (δ L : ℝ) ≤ C^(2*(L+1)) :=
    (hδbound L).trans (pow_le_pow_right₀ hC (by omega))
  obtain ⟨Q,P,hQ,hQdeg,hPdeg,htr,hcontact,hQbound,hPbound⟩ :=
    hκ r N t (δ L) f (b L) (C^(2*(L+1))) (C^(2*(L+1)))
      (hδ L) hsize (pow_nonneg (zero_le_one.trans hC) _) hδH (hb L) (hhouse L)
  have he : 2*(L+1) = (2*(2*r+1))*t := by rw [hL]; ring
  have hE : max 1 (κ * ((κ * ((N : ℝ)+1) * C^(2*(L+1))) ^
      (((r*t : ℕ) : ℝ) / (((N : ℝ)+1) - ((r*t : ℕ) : ℝ))))) =
      max 1 (κ^2 * ((2*r*t : ℕ) : ℝ) * C^(2*(L+1))) := by
    simpa only [N, Nat.cast_add, Nat.cast_one] using
      (typeII_balanced_kernel_bound κ (C^(2*(L+1))) r t hr ht)
  simp only [Nat.cast_add, Nat.cast_one] at hQbound hPbound
  rw [hE] at hQbound hPbound
  have hdimR : (N : ℝ)+1 = ((2*r*t : ℕ) : ℝ) := by exact_mod_cast hdim
  simp only [he, hdimR] at hQbound hPbound
  obtain ⟨hqb,hpb⟩ := hbound t ht
  refine ⟨Q,P,hQ,hQdeg,hPdeg,?_,?_,?_,?_⟩
  · simpa only [hdim] using htr
  · intro j n hn
    exact hcontact j n (by simpa only [← hL, L, Nat.add_assoc] using hn)
  · intro n
    exact (hQbound n).trans hqb
  · intro j n
    exact (hPbound j n).trans hpb

end StrictEUnit
end
