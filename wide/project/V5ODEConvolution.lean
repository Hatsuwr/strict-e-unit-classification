import V5ODEMajorant
import Mathlib.Tactic.Ring
import Mathlib.Analysis.RCLike.Basic

namespace StrictEUnit

/-- The convolution majorant yields a radius-weighted prefix estimate. -/
theorem v5_convolution_weighted_bound (a b : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (hrec : ∀ n : ℕ, (n + 1 : ℝ) * a (n + 1) ≤
      ∑ j ∈ Finset.range (n + 1), b j * a (n - j))
    {s : ℝ} (hs : 0 < s) (hbs : Summable (fun j => b j * s ^ j))
    (n : ℕ) (M : ℝ) (hM : ∀ i ≤ n, a i * s ^ i ≤ M) :
    (n + 1 : ℝ) * (a (n + 1) * s ^ (n + 1)) ≤
      (s * ∑' j, b j * s ^ j) * M := by
  have hM0 : 0 ≤ M := (mul_nonneg (ha 0) (pow_nonneg hs.le 0)).trans (hM 0 (Nat.zero_le n))
  calc
    (n + 1 : ℝ) * (a (n + 1) * s ^ (n + 1)) ≤
        (∑ j ∈ Finset.range (n + 1), b j * a (n - j)) * s ^ (n + 1) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hrec n) (pow_nonneg hs.le (n+1))
    _ = ∑ j ∈ Finset.range (n + 1), s * (b j * s ^ j) * (a (n-j) * s ^ (n-j)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hp : s ^ (n + 1) = s * (s ^ j * s ^ (n-j)) := by
        rw [← pow_add, Nat.add_sub_of_le hjn, pow_succ]; ring
      rw [hp]; ring
    _ ≤ ∑ j ∈ Finset.range (n+1), s * (b j * s ^ j) * M := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hM (n-j) (Nat.sub_le _ _))
        (mul_nonneg hs.le (mul_nonneg (hb j) (pow_nonneg hs.le j)))
    _ = (s * ∑ j ∈ Finset.range (n+1), b j * s ^ j) * M := by
      rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ (s * ∑' j, b j * s ^ j) * M := by
      apply mul_le_mul_of_nonneg_right _ hM0
      apply mul_le_mul_of_nonneg_left _ hs.le
      exact hbs.sum_le_tsum _ (fun j _ => mul_nonneg (hb j) (pow_nonneg hs.le j))

/-- The actual algebra-valued coefficient recurrence implies its scalar norm majorant.
No commutativity of the algebra is required. -/
theorem v5_ode_convolution_norm_bound
    {𝕜 A : Type*} [RCLike 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
    (D U : ℕ → A)
    (hrec : ∀ n : ℕ, ((n + 1 : ℕ) : 𝕜) • U (n + 1) =
      ∑ j ∈ Finset.range (n + 1), D j * U (n - j)) (n : ℕ) :
    (n + 1 : ℝ) * ‖U (n + 1)‖ ≤
      ∑ j ∈ Finset.range (n + 1), ‖D j‖ * ‖U (n - j)‖ := by
  calc
    (n + 1 : ℝ) * ‖U (n + 1)‖ = ‖((n + 1 : ℕ) : 𝕜) • U (n + 1)‖ := by
      rw [norm_smul, RCLike.norm_natCast]
      simp only [Nat.cast_add, Nat.cast_one]
    _ = ‖∑ j ∈ Finset.range (n + 1), D j * U (n - j)‖ := congrArg norm (hrec n)
    _ ≤ ∑ j ∈ Finset.range (n + 1), ‖D j * U (n - j)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (n + 1), ‖D j‖ * ‖U (n - j)‖ :=
      Finset.sum_le_sum (fun j _ => norm_mul_le _ _)

/-- The ODE convolution with an everywhere absolutely convergent coefficient
sequence has an everywhere absolutely convergent solution coefficient sequence. -/
theorem v5_ode_convolution_summable
    {𝕜 A : Type*} [RCLike 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
    (D U : ℕ → A)
    (hrec : ∀ n : ℕ, ((n + 1 : ℕ) : 𝕜) • U (n + 1) =
      ∑ j ∈ Finset.range (n + 1), D j * U (n - j))
    (hD : ∀ s : ℝ, 0 < s → Summable (fun j => ‖D j‖ * s ^ j))
    (r : ℝ) (hr : 0 ≤ r) : Summable (fun n => ‖U n‖ * r ^ n) := by
  apply v5_ode_majorant_summable (fun n => ‖U n‖) (fun n => norm_nonneg _) _ r hr
  intro s hs
  refine ⟨s * ∑' j, ‖D j‖ * s ^ j, ?_⟩
  intro n M hM
  exact v5_convolution_weighted_bound (fun n => ‖U n‖) (fun j => ‖D j‖)
    (fun n => norm_nonneg _) (fun j => norm_nonneg _)
    (v5_ode_convolution_norm_bound D U hrec) hs (hD s hs) n M hM

/-- The standard formal multilinear series associated to the actual ODE
coefficients has infinite convergence radius. -/
theorem v5_ode_convolution_radius_eq_top
    {𝕜 A : Type*} [RCLike 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
    (D U : ℕ → A)
    (hrec : ∀ n : ℕ, ((n + 1 : ℕ) : 𝕜) • U (n + 1) =
      ∑ j ∈ Finset.range (n + 1), D j * U (n - j))
    (hD : ∀ s : ℝ, 0 < s → Summable (fun j => ‖D j‖ * s ^ j)) :
    FormalMultilinearSeries.radius (fun n => ContinuousMultilinearMap.mkPiRing 𝕜 (Fin n) (U n)) = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  simpa only [ContinuousMultilinearMap.norm_mkPiRing] using
    v5_ode_convolution_summable D U hrec hD r r.2

end StrictEUnit
#print axioms StrictEUnit.v5_convolution_weighted_bound
#print axioms StrictEUnit.v5_ode_convolution_norm_bound
#print axioms StrictEUnit.v5_ode_convolution_summable
#print axioms StrictEUnit.v5_ode_convolution_radius_eq_top
