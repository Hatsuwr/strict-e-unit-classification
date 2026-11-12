import LogJetLCMDoubling

noncomputable section
open scoped BigOperators
namespace StrictEUnit

theorem logJet_central_choose_le_four_pow (n : ℕ) : (2*n).choose n≤4^n := by
  calc
    (2*n).choose n≤∑ k∈Finset.range (2*n+1),(2*n).choose k :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    _ = 2^(2*n) := Nat.sum_range_choose _
    _ = 4^n := by rw [pow_mul];norm_num

/-- A deliberately nonsharp elementary bound for the actual prefix LCM.
The proof is by doubling, using the proved Kummer/binomial divisibility. -/
theorem logJetLCM_le_sixteen_pow (N : ℕ) : logJetLCM N≤16^N := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hN : N=0
    · subst N;simp [logJetLCM]
    let n := N/2
    have hnN : n<N := Nat.div_lt_self (Nat.pos_of_ne_zero hN) (by decide)
    have hprev : logJetLCM n≤16^n := ih n hnN
    have hdouble : logJetLCM (2*n)≤4^n*16^n :=
      (logJetLCM_doubling_le n).trans (Nat.mul_le_mul (logJet_central_choose_le_four_pow n) hprev)
    have hcases : N=2*n ∨ N=2*n+1 := by dsimp only [n];omega
    rcases hcases with hEven | hOdd
    · rw [hEven]
      apply hdouble.trans
      calc
        4^n*16^n≤16^n*16^n := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by decide : 4≤16) n)
        _ = 16^(2*n) := by rw [two_mul,pow_add]
    · rw [hOdd,logJetLCM]
      have hlcm : Nat.lcm (2*n+1) (logJetLCM (2*n))≤(2*n+1)*logJetLCM (2*n) :=
        Nat.le_of_dvd (Nat.mul_pos (by omega) (logJetLCM_pos _)) (Nat.lcm_dvd_mul _ _)
      have hend : 2*n+1≤4^(n+1) := by
        calc
          2*n+1≤2^(2*n+1) := Nat.le_of_lt (Nat.lt_two_pow_self (n:=2*n+1))
          _ ≤2^(2*(n+1)) := Nat.pow_le_pow_right (by decide) (by omega)
          _ =4^(n+1) := by rw [pow_mul];norm_num
      calc
        Nat.lcm (2*n+1) (logJetLCM (2*n))≤(2*n+1)*logJetLCM (2*n) := hlcm
        _ ≤4^(n+1)*(4^n*16^n) := Nat.mul_le_mul hend hdouble
        _ =4*16^(2*n) := by
          calc
            4^(n+1)*(4^n*16^n)=4*((4*4*16 : ℕ)^n) := by
              simp only [pow_succ,mul_pow];ring
            _ =4*((16 : ℕ)^2)^n := by norm_num
            _ =4*16^(2*n) := by rw [pow_mul]
        _ ≤16*16^(2*n) := Nat.mul_le_mul_right _ (by decide : 4≤16)
        _ =16^(2*n+1) := by rw [pow_succ];ring

theorem logJetLCM_real_le_sixteen_pow (N : ℕ) : (logJetLCM N : ℝ)≤16^N := by
  exact_mod_cast logJetLCM_le_sixteen_pow N

end StrictEUnit
end
