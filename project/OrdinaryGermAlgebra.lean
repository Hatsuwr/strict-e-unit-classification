import OrdinaryGermDerivatives
import Mathlib.Analysis.Normed.Ring.InfiniteSum

noncomputable section
open scoped Topology BigOperators
namespace StrictEUnit

/-- Formal multiplication is exactly the ordinary Cauchy product at a point. -/
theorem ordinary_coeff_mul_term (P Q : PowerSeries ℂ) (z : ℂ) (n : ℕ) :
    PowerSeries.coeff ℂ n (P*Q) * z^n =
      ∑ k ∈ Finset.range (n+1),
        (PowerSeries.coeff ℂ k P * z^k) *
          (PowerSeries.coeff ℂ (n-k) Q * z^(n-k)) := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun k l : ℕ => PowerSeries.coeff ℂ k P * PowerSeries.coeff ℂ l Q) n,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.1 hk)
  have hz : z^k*z^(n-k)=z^n := by rw [← pow_add,Nat.add_sub_of_le hkn]
  calc
    _ = (PowerSeries.coeff ℂ k P * PowerSeries.coeff ℂ (n-k) Q) *
        (z^k*z^(n-k)) := by rw [hz]
    _ = _ := by ring

theorem hasFPowerSeriesAt_mul_ofScalars (f g : ℂ → ℂ) (P Q : PowerSeries ℂ)
    (hf : HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n P)) 0)
    (hg : HasFPowerSeriesAt g
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n Q)) 0) :
    HasFPowerSeriesAt (fun z => f z*g z)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n (P*Q))) 0 := by
  obtain ⟨R,hf⟩ := hf
  obtain ⟨S,hg⟩ := hg
  apply hasFPowerSeriesAt_iff.2
  filter_upwards [EMetric.ball_mem_nhds (0:ℂ) (lt_min hf.r_pos hg.r_pos)] with z hz
  have hzR : z ∈ EMetric.ball (0:ℂ) R  := by
    exact EMetric.mem_ball.mpr (lt_of_lt_of_le (EMetric.mem_ball.mp hz) (min_le_left R S))
  have hzS : z ∈ EMetric.ball (0:ℂ) S  := by
    exact EMetric.mem_ball.mpr (lt_of_lt_of_le (EMetric.mem_ball.mp hz) (min_le_right R S))
  have hsP := (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n P)).summable_norm_apply
    (EMetric.mem_ball.mpr (lt_of_lt_of_le (EMetric.mem_ball.mp hzR) hf.r_le))
  have hsQ := (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n Q)).summable_norm_apply
    (EMetric.mem_ball.mpr (lt_of_lt_of_le (EMetric.mem_ball.mp hzS) hg.r_le))
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] at hsP hsQ
  have hfz := hf.hasSum hzR
  have hgz := hg.hasSum hzS
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] at hfz hgz
  have hm := hasSum_sum_range_mul_of_summable_norm hsP hsQ
  rw [hfz.tsum_eq,hgz.tsum_eq] at hm
  simp only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, zero_add]
  convert hm using 1
  funext n
  rw [mul_comm]
  exact ordinary_coeff_mul_term P Q z n

theorem hasFPowerSeriesAt_add_ofScalars (f g : ℂ → ℂ) (P Q : PowerSeries ℂ)
    (hf : HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n P)) 0)
    (hg : HasFPowerSeriesAt g
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n Q)) 0) :
    HasFPowerSeriesAt (fun z => f z+g z)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n (P+Q))) 0 := by
  have he : (fun n => PowerSeries.coeff ℂ n (P+Q)) =
      (fun n => PowerSeries.coeff ℂ n P) + (fun n => PowerSeries.coeff ℂ n Q) := by
    funext n
    exact map_add (PowerSeries.coeff ℂ n) P Q
  rw [he,FormalMultilinearSeries.ofScalars_add]
  exact hf.add hg

theorem hasFPowerSeriesAt_polynomial_ofScalars (p : Polynomial ℂ) :
    HasFPowerSeriesAt (fun z => p.eval z)
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => PowerSeries.coeff ℂ n (p:PowerSeries ℂ))) 0 := by
  classical
  apply hasFPowerSeriesAt_iff.2
  apply Filter.Eventually.of_forall
  intro z
  have hs : HasSum (fun n => p.coeff n*z^n) (∑ n ∈ p.support,p.coeff n*z^n) :=
    hasSum_sum_of_ne_finset_zero (fun n hn => by
      have hc : p.coeff n = 0 := by
        simpa only [Polynomial.mem_support_iff, not_not] using hn
      rw [hc,zero_mul])
  simpa only [FormalMultilinearSeries.coeff_ofScalars, Polynomial.coeff_coe,
    zero_add, smul_eq_mul, mul_comm, Polynomial.eval_eq_sum,Polynomial.sum_def] using hs

theorem hasFPowerSeriesAt_finset_sum_ofScalars {ι : Type*}
    (s : Finset ι) (f : ι → ℂ → ℂ) (P : ι → PowerSeries ℂ)
    (h : ∀ i ∈ s, HasFPowerSeriesAt (f i)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n (P i))) 0) :
    HasFPowerSeriesAt (fun z => ∑ i ∈ s,f i z)
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => PowerSeries.coeff ℂ n (∑ i ∈ s,P i))) 0 := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
    intro h
    apply hasFPowerSeriesAt_iff.2
    apply Filter.Eventually.of_forall
    intro z
    simp only [Finset.sum_empty, map_zero, FormalMultilinearSeries.coeff_ofScalars,
      smul_zero]
    exact hasSum_zero
  | @insert a s ha ih =>
    intro h
    have hsa := h a (Finset.mem_insert_self a s)
    have hss := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa only [Finset.sum_insert ha] using
      hasFPowerSeriesAt_add_ofScalars (f a) (fun z => ∑ i ∈ s,f i z)
        (P a) (∑ i ∈ s,P i) hsa hss

/-- Equal literal convergent series give actual local equality. -/
theorem eventually_eq_of_same_ordinary_series
    (f g : ℂ → ℂ) (P : PowerSeries ℂ)
    (hf : HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n P)) 0)
    (hg : HasFPowerSeriesAt g
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n P)) 0) :
    ∀ᶠ z in nhds (0:ℂ), f z=g z := by
  filter_upwards [hf.eventually_hasSum,hg.eventually_hasSum] with z hfz hgz
  simpa only [zero_add] using hfz.unique hgz

end StrictEUnit
end
