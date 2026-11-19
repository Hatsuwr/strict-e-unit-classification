import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace StrictEUnit
/-- A prefix-bound version of the ODE coefficient majorant. -/
theorem v5_ode_majorant_bounded (a : ℕ → ℝ) (C : ℝ)
    (ha : ∀ n, 0 ≤ a n)
    (hrec : ∀ n M, (∀ i ≤ n, a i ≤ M) →
      (n + 1 : ℝ) * a (n + 1) ≤ C * M) :
    ∃ M, 0 ≤ M ∧ ∀ n, a n ≤ M := by
  obtain ⟨N, hN⟩ := exists_nat_gt C
  let M := ∑ i ∈ Finset.range (N + 1), a i
  have hM : 0 ≤ M := Finset.sum_nonneg (fun i _ => ha i)
  refine ⟨M, hM, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n ≤ N
    · exact Finset.single_le_sum (fun i _ => ha i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 from by intro h; subst n; exact hn (Nat.zero_le N))
      have hprefix : ∀ i ≤ m, a i ≤ M := fun i hi => ih i (Nat.lt_succ_of_le hi)
      have hr := hrec m M hprefix
      have hnm : C ≤ (m + 1 : ℝ) := le_trans hN.le (by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hn)))
      have hpos : 0 < (m + 1 : ℝ) := by positivity
      nlinarith

/-- Direct adapter from the finite-prefix maximum formulation. -/
theorem v5_ode_prefixMax_majorant_bounded (a : ℕ → ℝ) (C : ℝ)
    (ha : ∀ n, 0 ≤ a n) (hC : 0 ≤ C)
    (hrec : ∀ n : ℕ, (n + 1 : ℝ) * a (n + 1) ≤
      C * (Finset.range (n + 1)).sup' (by simp) a) :
    ∃ M, 0 ≤ M ∧ ∀ n, a n ≤ M := by
  apply v5_ode_majorant_bounded a C ha
  intro n M hM
  apply (hrec n).trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply Finset.sup'_le
  intro i hi
  exact hM i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))

/-- Bounds at a larger radius give absolute summability at every smaller radius. -/
theorem v5_summable_of_weighted_bound (a : ℕ → ℝ) {r s M : ℝ}
    (ha : ∀ n, 0 ≤ a n) (hr : 0 ≤ r) (hrs : r < s)
    (hM : ∀ n, a n * s ^ n ≤ M) :
    Summable (fun n => a n * r ^ n) := by
  have hs : 0 < s := lt_of_le_of_lt hr hrs
  have hratio : 0 ≤ r / s := div_nonneg hr hs.le
  have hlt : r / s < 1 := (div_lt_one hs).mpr hrs
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (ha n) (pow_nonneg hr n)) _
    ((summable_geometric_of_lt_one hratio hlt).mul_left M)
  intro n
  calc
    a n * r ^ n = (a n * s ^ n) * (r / s) ^ n := by
      rw [mul_assoc, ← mul_pow, mul_div_cancel₀ r hs.ne']
    _ ≤ M * (r / s) ^ n := mul_le_mul_of_nonneg_right (hM n) (pow_nonneg hratio n)

/-- The weighted ODE recurrence at every positive radius implies absolute
summability on every finite radius. The constants may depend on the radius. -/
theorem v5_ode_majorant_summable (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hrec : ∀ s : ℝ, 0 < s → ∃ C : ℝ, ∀ (n : ℕ) (M : ℝ),
      (∀ i ≤ n, a i * s ^ i ≤ M) →
      (n + 1 : ℝ) * (a (n + 1) * s ^ (n + 1)) ≤ C * M)
    (r : ℝ) (hr : 0 ≤ r) : Summable (fun n => a n * r ^ n) := by
  obtain ⟨C, hC⟩ := hrec (r + 1) (by linarith)
  obtain ⟨M, _, hM⟩ := v5_ode_majorant_bounded (fun n => a n * (r + 1) ^ n) C
    (fun n => mul_nonneg (ha n) (pow_nonneg (by linarith) n)) hC
  exact v5_summable_of_weighted_bound a ha hr (by linarith : r < r + 1) hM

/-- A formal multilinear series satisfying the radius-wise ODE majorant
has genuinely infinite Mathlib convergence radius. -/
theorem v5_ode_majorant_radius_eq_top
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (p : FormalMultilinearSeries 𝕜 E F)
    (hrec : ∀ s : ℝ, 0 < s → ∃ C : ℝ, ∀ (n : ℕ) (M : ℝ),
      (∀ i ≤ n, ‖p i‖ * s ^ i ≤ M) →
      (n + 1 : ℝ) * (‖p (n + 1)‖ * s ^ (n + 1)) ≤ C * M) :
    p.radius = ⊤ := by
  apply p.radius_eq_top_of_summable_norm
  intro r
  exact v5_ode_majorant_summable (fun n => ‖p n‖) (fun n => norm_nonneg _) hrec r r.2

end StrictEUnit
#print axioms StrictEUnit.v5_ode_majorant_bounded
#print axioms StrictEUnit.v5_summable_of_weighted_bound
#print axioms StrictEUnit.v5_ode_majorant_summable
#print axioms StrictEUnit.v5_ode_majorant_radius_eq_top

#print axioms StrictEUnit.v5_ode_prefixMax_majorant_bounded
