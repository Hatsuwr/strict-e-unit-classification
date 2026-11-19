import V5BroadPowerArithmetic
import V5BroadSameMatrixDenominators
import OrdinaryDerivativePrefix
import Stage26ODERecurrenceCoefficients

noncomputable section
namespace StrictEUnit
open scoped NumberField BigOperators

private theorem v5_derivative_multiplier_bound (L r n i : ℕ) (hn : n ≤ L) (hi : i ≤ r) :
    (n+i).descFactorial i ≤ (2^(r*(r+2)))^(L+1) := by
  have hL : L+1 ≤ (2 : ℕ)^(L+1) := Nat.le_of_lt (L+1).lt_two_pow_self
  have hr : r+1 ≤ (2 : ℕ)^(r+1) := Nat.le_of_lt (r+1).lt_two_pow_self
  have hshift : n+i ≤ (2 : ℕ)^((r+2)*(L+1)) := by
    calc
      _ ≤ (r+1)*(L+1) := by nlinarith
      _ ≤ 2^(r+1)*2^(L+1) := Nat.mul_le_mul hr hL
      _ = 2^((r+1)+(L+1)) := (pow_add ..).symm
      _ ≤ _ := by
        apply Nat.pow_le_pow_right (by decide)
        nlinarith
  calc
    _ ≤ (n+i)^i := Nat.descFactorial_le_pow _ _
    _ ≤ (2^((r+2)*(L+1)))^i := Nat.pow_le_pow_left hshift _
    _ ≤ (2^((r+2)*(L+1)))^r :=
      Nat.pow_le_pow_right (by positivity) hi
    _ = _ := by simp only [← pow_mul]; congr 1; ring

private theorem v5_house_natCast {K : Type*} [Field K] [NumberField K] (n : ℕ) :
    NumberField.house (n : K) = (n : ℝ) := by
  simpa using (NumberField.house_intCast (K := K) (n : ℤ))

/-- Actual ordinary derivative prefixes inherit broad common integral
arithmetic; the certificate is selected afresh for each integer precision. -/
theorem v5_broad_ordinaryDerivativePrefix {K : Type*} [Field K] [NumberField K]
    (a : ℕ → K) (ha : V5BroadArithmetic a) (r : ℕ) :
    V5BroadIntegralPrefix K (ordinaryDerivativePrefix r (PowerSeries.mk a)) := by
  classical
  intro prec
  let k := prec+1
  obtain ⟨C,hC,δ,hδ,hδb,hab,hint⟩ :=
    v5_broad_arithmetic_power_bounds a ha (2*k) (by dsimp [k]; omega)
  have hmax (L : ℕ) : ∃ n ∈ Finset.range (L+r+1),
      ∀ n' ∈ Finset.range (L+r+1), NumberField.house (a n') ≤ NumberField.house (a n) :=
    Finset.exists_max_image _ _ ⟨0, by simp⟩
  choose idx hidx hmax using hmax
  let M (L : ℕ) := max 1 (NumberField.house (a (idx L)))
  let F : ℝ := (2:ℝ)^(r*(r+2))
  let H (L : ℕ) := F^(L+1) * (δ (L+r) : ℝ) * M L
  have hF : 1 ≤ F := one_le_pow₀ (by norm_num)
  have hM (L : ℕ) : 1 ≤ M L := le_max_left _ _
  have hδone (L : ℕ) : (1 : ℝ) ≤ δ L := by exact_mod_cast hδ L
  have hH (L : ℕ) : 1 ≤ H L :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hF) (hδone _)) (hM L)
  have hhouse (L n : ℕ) (hn : n ≤ L+r) : NumberField.house (a n) ≤ M L :=
    (hmax L n (Finset.mem_range.mpr (by omega))).trans (le_max_right _ _)
  have hR (L : ℕ) : 1 ≤ C^(L+r+1)*((L+r).factorial : ℝ) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC)
      (by exact_mod_cast Nat.factorial_pos (L+r))
  have hMp (L : ℕ) : (M L)^(2*k) ≤ C^(L+r+1)*((L+r).factorial : ℝ) := by
    rcases le_total (NumberField.house (a (idx L))) 1 with hh | hh
    · simpa only [M, max_eq_left hh, one_pow] using hR L
    · dsimp only [M]
      rw [max_eq_right hh]
      have hn : idx L ≤ L+r := by have := Finset.mem_range.mp (hidx L); omega
      exact (hab (idx L)).trans (mul_le_mul
        (pow_le_pow_right₀ hC (by omega))
        (by exact_mod_cast Nat.factorial_le hn)
        (by positivity) (by positivity))
  have hDM (L : ℕ) :
      ((δ (L+r) : ℝ)*M L)^k ≤ C^(L+r+1)*((L+r).factorial : ℝ) := by
    apply le_of_pow_le_pow_left₀ (n := 2) (by decide) (by positivity)
    rw [← pow_mul, Nat.mul_comm k 2, mul_pow, pow_two]
    exact mul_le_mul (hδb (L+r)) (hMp L) (by positivity) (by positivity)
  let f := ordinaryDerivativePrefix r (PowerSeries.mk a)
  have hcoeff (i : Fin r) (n : ℕ) :
      PowerSeries.coeff K n (f i) = ((n+i.val).descFactorial i.val : K)*a (n+i.val) := by
    change PowerSeries.coeff K n ((PowerSeries.derivative K)^[i.val] (PowerSeries.mk a)) = _
    rw [stage26_coeff_iterate_derivative, descPochhammer_eval_eq_descFactorial, PowerSeries.coeff_mk]
  have hiint (L : ℕ) (i : Fin r) (n : ℕ) (hn : n ≤ L) :
      IsIntegral ℤ ((δ (L+r) : K)*PowerSeries.coeff K n (f i)) := by
    rw [hcoeff]
    have ha' := hint (L+r) (n+i.val) (by have := i.isLt; omega)
    have hnat : IsIntegral ℤ (((n+i.val).descFactorial i.val : ℕ) : K) := by
      simpa using (isIntegral_algebraMap (R := ℤ) (A := K) (x := (((n+i.val).descFactorial i.val : ℕ) : ℤ)))
    convert hnat.mul ha' using 1; ring
  let b (L : ℕ) (i : Fin r) (n : ℕ) : 𝓞 K :=
    if hn : n ≤ L then ⟨(δ (L+r) : K)*PowerSeries.coeff K n (f i), hiint L i n hn⟩ else 0
  have hb (L : ℕ) (i : Fin r) (n : ℕ) (hn : n ≤ L) :
      (b L i n : K) = (δ (L+r) : K)*PowerSeries.coeff K n (f i) := by simp [b, hn]
  have hbh (L : ℕ) (i : Fin r) (n : ℕ) (hn : n ≤ L) :
      NumberField.house (b L i n : K) ≤ H L := by
    rw [hb L i n hn, hcoeff]
    have hc : (((n+i.val).descFactorial i.val : ℕ) : ℝ) ≤ F^(L+1) := by
      dsimp only [F]
      exact_mod_cast v5_derivative_multiplier_bound L r n i.val hn (Nat.le_of_lt i.isLt)
    calc
      _ ≤ (δ (L+r) : ℝ) * NumberField.house (((n+i.val).descFactorial i.val : K)*a (n+i.val)) := by
        simpa only [v5_house_natCast] using NumberField.house_mul_le (δ (L+r) : K) _
      _ ≤ (δ (L+r) : ℝ) * ((((n+i.val).descFactorial i.val : ℕ) : ℝ)*NumberField.house (a (n+i.val))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [v5_house_natCast] using NumberField.house_mul_le ((n+i.val).descFactorial i.val : K) _
      _ ≤ (δ (L+r) : ℝ) * (F^(L+1)*M L) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul hc (hhouse L (n+i.val) (by have := i.isLt; omega))
          (NumberField.house_nonneg _) (by positivity)
      _ = _ := by dsimp [H]; ring
  refine ⟨F^k*C^(r+1)*F, ?_, (fun L => δ (L+r)), b, H, (fun L => hδ _), hH, ?_, hb, hbh, ?_⟩
  · exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hF) (one_le_pow₀ hC)) hF
  · intro L
    have hh := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hF (n := L+1)) (hM L)
    have := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (δ (L+r)))
    dsimp [H]
    nlinarith
  · intro L
    have hshift : ((L+r).factorial : ℝ) ≤ F^(L+1)*(L.factorial : ℝ) := by
      dsimp only [F]
      exact_mod_cast v5_factorial_shift_bound L r
    have hCshift : C^(L+r+1) ≤ (C^(r+1))^(L+1) := by
      rw [← pow_mul]
      apply pow_le_pow_right₀ hC
      nlinarith
    calc
      (H L)^prec ≤ (H L)^k := pow_le_pow_right₀ (hH L) (by dsimp [k]; omega)
      _ = (F^k)^(L+1)*(((δ (L+r) : ℝ)*M L)^k) := by dsimp [H]; simp only [mul_pow, ← pow_mul]; rw [Nat.mul_comm (L+1) k]; ring
      _ ≤ (F^k)^(L+1)*(C^(L+r+1)*((L+r).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left (hDM L) (by positivity)
      _ ≤ (F^k)^(L+1)*((C^(r+1))^(L+1)*(F^(L+1)*(L.factorial : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hCshift hshift (by positivity) (by positivity)) (by positivity)
      _ = _ := by simp only [mul_pow]; ring

#print axioms v5_broad_ordinaryDerivativePrefix
end StrictEUnit
end
