import FallingLogJetArithmetic
import IntegralNormHouse
import Mathlib.Data.Nat.Choose.Bounds

noncomputable section
open scoped BigOperators NumberField
namespace StrictEUnit

variable {K L : Type*} [Field K] [Field L] [CharZero K] [CharZero L]

theorem field_choose_succ_ratio (x : K) (m : ℕ) :
    Ring.choose x (m+1)=Ring.choose x m*(x-(m : K))/((m+1 : ℕ) : K) := by
  simp only [field_choose_eq_descPochhammer_div,descPochhammer_succ_eval,Nat.factorial_succ,Nat.cast_mul]
  ring

theorem field_choose_map (phi : K →+* L) (x : K) (m : ℕ) :
    phi (Ring.choose x m)=Ring.choose (phi x) m := by
  induction m with
  | zero => simp only [Ring.choose_zero_right,map_one]
  | succ m ih =>
    simp only [field_choose_succ_ratio,map_div₀,map_mul,map_sub,map_natCast,ih]

/-- A simple geometric bound at a fixed complex argument. -/
theorem complex_choose_norm_le (x : ℂ) (m : ℕ) :
    ‖Ring.choose x m‖≤(‖x‖+1)^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [field_choose_succ_ratio,norm_div,norm_mul,Complex.norm_natCast]
    have hden : (0 : ℝ)<((m+1 : ℕ) : ℝ) := by positivity
    apply (div_le_iff₀ hden).2
    have hb : ‖x-(m : ℂ)‖≤(‖x‖+1)*((m+1 : ℕ) : ℝ) := by
      have h := norm_sub_le x (m : ℂ)
      rw [Complex.norm_natCast] at h
      have hx := norm_nonneg x
      push_cast
      nlinarith
    calc
      ‖Ring.choose x m‖*‖x-(m : ℂ)‖≤(‖x‖+1)^m*((‖x‖+1)*((m+1 : ℕ) : ℝ)) :=
        mul_le_mul ih hb (norm_nonneg _) (pow_nonneg (by positivity) _)
      _ = (‖x‖+1)^(m+1)*((m+1 : ℕ) : ℝ) := by rw [pow_succ];ring

/-- Uniform in BOTH the binomial order and an integer translation. -/
theorem complex_choose_nat_translate_norm_le (x : ℂ) (m n N : ℕ)
    (hm : m≤N) (hn : n≤N) :
    ‖Ring.choose (x+(n : ℂ)) m‖≤(4*(‖x‖+1))^(N+1) := by
  rw [Ring.add_choose_eq _ (Commute.all _ _)]
  have hc : 1≤‖x‖+1 := by have := norm_nonneg x;linarith
  have hnat (b : ℕ) : (n.choose b : ℝ)≤2^n := by
    have h : n.choose b≤2^n := by
      calc
        n.choose b ≤ ∑ k ∈ Finset.range (n+1),n.choose k := by
          by_cases hb : b≤n
          · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
          · rw [Nat.choose_eq_zero_of_lt (by omega)];exact Nat.zero_le _
        _ = 2^n := Nat.sum_range_choose n
    exact_mod_cast h
  calc
    ‖∑ ab ∈ Finset.antidiagonal m,Ring.choose x ab.1*Ring.choose (n : ℂ) ab.2‖ ≤
        ∑ _ab ∈ Finset.antidiagonal m,(‖x‖+1)^N*(2 : ℝ)^N := by
      apply norm_sum_le_of_le
      rintro ⟨a,b⟩ hab
      rw [norm_mul,Ring.choose_natCast,Complex.norm_natCast]
      have hab' := Finset.mem_antidiagonal.mp hab
      apply mul_le_mul ((complex_choose_norm_le x a).trans (pow_le_pow_right₀ hc (by omega)))
        ((hnat b).trans (pow_le_pow_right₀ (by norm_num) hn)) (Nat.cast_nonneg _) (pow_nonneg (by positivity) _)
    _ = ((m+1 : ℕ) : ℝ)*((‖x‖+1)^N*(2 : ℝ)^N) := by simp
    _ ≤ (2 : ℝ)^(N+1)*((‖x‖+1)^N*(2 : ℝ)^N) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have h : m+1≤2^(N+1) := (by omega : m+1≤N+1).trans (Nat.le_of_lt (Nat.lt_two_pow_self (n:=N+1)))
      exact_mod_cast h
    _ ≤ (4*(‖x‖+1))^(N+1) := by
      have hp := pow_le_pow_right₀ hc (Nat.le_succ N)
      have ht := pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2) (Nat.le_succ N)
      calc
        (2 : ℝ)^(N+1)*((‖x‖+1)^N*(2 : ℝ)^N) ≤
          (2 : ℝ)^(N+1)*((‖x‖+1)^(N+1)*(2 : ℝ)^(N+1)) := by gcongr
        _ = (4*(‖x‖+1))^(N+1) := by rw [show (4 : ℝ)=2*2 by norm_num];simp only [mul_pow];ring

/-- One base controls every embedding of a number field. -/
theorem numberField_choose_nat_translate_house_le [NumberField K]
    (x : K) (m n N : ℕ) (hm : m≤N) (hn : n≤N) :
    NumberField.house (Ring.choose (x+(n : K)) m)≤(4*(NumberField.house x+1))^(N+1) := by
  unfold NumberField.house
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro sigma
  change ‖sigma (Ring.choose (x+(n : K)) m)‖≤_
  rw [field_choose_map,map_add,map_natCast]
  exact (complex_choose_nat_translate_norm_le (sigma x) m n N hm hn).trans
    (pow_le_pow_left₀ (by positivity) (by
      have h := norm_le_pi_norm (NumberField.canonicalEmbedding K x) sigma
      change ‖sigma x‖≤‖NumberField.canonicalEmbedding K x‖ at h
      linarith) _)

end StrictEUnit
end
