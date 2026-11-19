import RationalEulerLogComparison

noncomputable section
open scoped NumberField Topology BigOperators
open NumberField Finset Filter
namespace StrictEUnit

theorem galois_prime_tsum_constraint_of_complement_summable
    (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    [DecidablePred (GaloisCompletelySplitAt K)]
    (hcomp : Summable (fun p : ℕ => if p.Prime ∧ ¬GaloisCompletelySplitAt K p
      then 1 / (p : ℝ) else 0)) :
    ∃ C E : ℝ, 0 < C ∧ ∀ s : ℝ, 1 < s →
      (Module.finrank ℚ K : ℝ) * (∑' p : Nat.Primes, 1 / (p : ℝ)^s) ≤
        Real.log (s*C/(s-1)) + E := by
  classical
  obtain ⟨C,E,hC,h⟩ := galois_prime_sum_constraint_of_complement_summable K hcomp
  refine ⟨C,E,hC,?_⟩
  intro s hs
  rw [← tsum_mul_left]
  apply ((prime_reciprocal_rpow_summable hs).mul_left (Module.finrank ℚ K : ℝ)).tsum_le_of_sum_le
  intro S
  have hp : ∀ p ∈ S.image (fun p : Nat.Primes => (p : ℕ)), p.Prime := by
    intro p hp
    obtain ⟨q,_,rfl⟩ := mem_image.mp hp
    exact q.prop
  have hb := h s hs _ hp
  rw [sum_image (f := fun p : ℕ => 1 / (p : ℝ)^s) (g := fun p : Nat.Primes => (p : ℕ))
      (fun a _ b _ hab => Subtype.ext hab), mul_sum] at hb
  exact hb

theorem galois_nonsplit_reciprocal_not_summable
    (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    [DecidablePred (GaloisCompletelySplitAt K)] (hd : 1 < Module.finrank ℚ K) :
    ¬Summable (fun p : ℕ => if p.Prime ∧ ¬GaloisCompletelySplitAt K p
      then 1 / (p : ℝ) else 0) := by
  intro hcomp
  obtain ⟨C,E,hC,hbound⟩ := galois_prime_tsum_constraint_of_complement_summable K hcomp
  let d : ℝ := Module.finrank ℚ K
  have hd' : 1 < d := by dsimp [d]; exact_mod_cast hd
  let A : ℝ := 2 * (∑' n : ℕ, 1 / (n : ℝ)^2)
  let B : ℝ := Real.log (2*C) + E + d*A - d*Real.log (1/2)
  have hnear : ∀ᶠ s : ℝ in 𝓝[>] 1, (d-1)*(-Real.log (s-1)) ≤ B := by
    filter_upwards [rational_zeta_pole_lower, self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (1:ℝ)<2)).filter_mono nhdsWithin_le_nhds] with s hz hs hs2
    have hp : 0 < s-1 := sub_pos.mpr hs
    have hloglow := Real.log_le_log (div_pos (by norm_num : (0:ℝ)<1/2) hp) hz
    rw [Real.log_div (by norm_num : (1/2:ℝ) ≠ 0) hp.ne'] at hloglow
    have hlogup := rational_zeta_log_le_prime_sum hs
    have hall := hbound s hs
    have hcprod : s*C/(s-1) ≤ (2*C)/(s-1) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hs2.le hC.le) hp.le
    have hlC := Real.log_le_log (div_pos (mul_pos (by linarith) hC) hp) hcprod
    have hlogeq : Real.log (2*C/(s-1)) = Real.log (2*C) - Real.log (s-1) :=
      Real.log_div (mul_ne_zero (by norm_num) hC.ne') hp.ne'
    rw [hlogeq] at hlC
    have hm := mul_le_mul_of_nonneg_left (hloglow.trans hlogup) (by linarith : 0 ≤ d)
    change Real.log (∑' n : ℕ, 1 / (n : ℝ)^s) ≤ _ + A at hlogup
    change d * _ ≤ _ at hall
    dsimp [B, A]
    nlinarith
  have hsub : Tendsto (fun s : ℝ => s-1) (𝓝[>] 1) (𝓝[>] 0) := by
    have hcont : Continuous (fun s : ℝ => s-1) := continuous_id.sub continuous_const
    simpa using (hcont.continuousWithinAt (x := 1) (s := Set.Ioi 1)).tendsto_nhdsWithin (fun s hs => sub_pos.mpr hs)
  have hsmall := (Real.tendsto_log_nhdsGT_zero.comp hsub).eventually
    (eventually_lt_atBot (-(B+1)/(d-1)))
  obtain ⟨s, hs, hsmall⟩ := (hnear.and hsmall).exists
  have h := (lt_div_iff₀ (by linarith : 0 < d-1)).mp hsmall
  simp only [Function.comp_apply] at h
  nlinarith

end StrictEUnit
end
