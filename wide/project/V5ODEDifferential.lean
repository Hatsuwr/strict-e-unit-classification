import Mathlib.Analysis.Calculus.Deriv.Pow
import V5ODESeries
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum

noncomputable section
namespace StrictEUnit

/-- The actual scalar-power series associated to algebra coefficients. -/
def v5ODESum {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (U : ℕ → A) (z : ℂ) : A := ∑' n, z ^ n • U n

theorem v5_ode_derivative_weights_summable
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (D U : ℕ → A)
    (hrec : ∀ n : ℕ, ((n + 1 : ℕ) : ℂ) • U (n + 1) =
      ∑ j ∈ Finset.range (n + 1), D j * U (n - j))
    {s : ℝ} (hs : 0 ≤ s)
    (hD : Summable (fun n => ‖D n‖ * s ^ n))
    (hU : Summable (fun n => ‖U n‖ * s ^ n)) :
    Summable (fun n : ℕ => (n + 1 : ℝ) * ‖U (n+1)‖ * s ^ n) := by
  have hDn : Summable (fun n => ‖‖D n‖ * s ^ n‖) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hs _))] using hD
  have hUn : Summable (fun n => ‖‖U n‖ * s ^ n‖) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hs _))] using hU
  apply Summable.of_nonneg_of_le (fun n => by positivity) _
    (summable_sum_mul_range_of_summable_norm' hDn hD hUn hU)
  intro n
  calc
    (n+1 : ℝ) * ‖U (n+1)‖ * s ^ n ≤
        (∑ j ∈ Finset.range (n+1), ‖D j‖ * ‖U (n-j)‖) * s ^ n :=
      mul_le_mul_of_nonneg_right (v5_ode_convolution_norm_bound D U hrec n) (pow_nonneg hs n)
    _ = ∑ j ∈ Finset.range (n+1), (‖D j‖ * s ^ j) * (‖U (n-j)‖ * s ^ (n-j)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hp : s ^ n = s ^ j * s ^ (n-j) := by rw [← pow_add, Nat.add_sub_of_le hjn]
      rw [hp]; ring

theorem v5_ode_terms_summable
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (U : ℕ → A) (z : ℂ) (hU : Summable (fun n => ‖U n‖ * ‖z‖ ^ n)) :
    Summable (fun n => z ^ n • U n) := by
  apply Summable.of_norm
  simpa only [norm_smul, norm_pow, mul_comm] using hU

/-- Differentiation of the summed ODE series, first in coefficient form. -/
theorem v5_ode_sum_hasDerivAt_series
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (D U : ℕ → A)
    (hrec : ∀ n : ℕ, ((n + 1 : ℕ) : ℂ) • U (n + 1) =
      ∑ j ∈ Finset.range (n + 1), D j * U (n - j))
    (hD : ∀ s : ℝ, 0 ≤ s → Summable (fun n => ‖D n‖ * s ^ n))
    (hU : ∀ s : ℝ, 0 ≤ s → Summable (fun n => ‖U n‖ * s ^ n)) (z : ℂ) :
    HasDerivAt (v5ODESum U)
      (∑' n : ℕ, (((n+1 : ℕ) : ℂ) * z ^ n) • U (n+1)) z := by
  let s : ℝ := ‖z‖ + 1
  have hs : 0 < s := by dsimp [s]; positivity
  have hw := v5_ode_derivative_weights_summable D U hrec hs.le (hD s hs.le) (hU s hs.le)
  have hd : HasDerivAt (fun y : ℂ => ∑' n : ℕ, y ^ (n+1) • U (n+1))
      (∑' n : ℕ, (((n+1 : ℕ) : ℂ) * z ^ n) • U (n+1)) z := by
    apply hasDerivAt_tsum_of_isPreconnected
      (g := fun n y => y ^ (n+1) • U (n+1))
      (g' := fun n y => (((n+1 : ℕ) : ℂ) * y ^ n) • U (n+1))
      (y₀ := (0 : ℂ)) (t := Metric.ball 0 s) hw Metric.isOpen_ball
      (convex_ball (0 : ℂ) s).isPreconnected
    · intro n y hy
      simpa only [Nat.add_sub_cancel, id_eq, mul_one] using ((hasDerivAt_id y).pow (n+1)).smul_const (U (n+1))
    · intro n y hy
      have hyn : ‖y‖ ≤ s := le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hy)
      calc
        ‖(((n+1 : ℕ) : ℂ) * y ^ n) • U (n+1)‖ =
            (n+1 : ℝ) * ‖U (n+1)‖ * ‖y‖ ^ n := by
          rw [norm_smul, norm_mul, Complex.norm_natCast, norm_pow]
          push_cast; ring
        _ ≤ (n+1 : ℝ) * ‖U (n+1)‖ * s ^ n :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hyn n) (by positivity)
    · exact Metric.mem_ball_self hs
    · simp only [zero_pow (Nat.succ_ne_zero _), zero_smul, summable_zero]
    · change dist z 0 < s
      simp only [dist_zero_right]; dsimp [s]; linarith
  have he : v5ODESum U = fun y : ℂ => U 0 + ∑' n : ℕ, y ^ (n+1) • U (n+1) := by
    funext y
    have ht := (v5_ode_terms_summable U y (hU ‖y‖ (norm_nonneg y))).tsum_eq_zero_add
    simpa only [v5ODESum, pow_zero, one_smul] using ht
  rw [he]
  exact hd.const_add (U 0)

/-- Cauchy multiplication identifies the summed derivative coefficients with
left multiplication by the summed ODE coefficient function. -/
theorem v5_ode_derivative_series_eq_product
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (D U : ℕ → A)
    (hrec : ∀ n : ℕ, ((n + 1 : ℕ) : ℂ) • U (n + 1) =
      ∑ j ∈ Finset.range (n + 1), D j * U (n - j))
    (z : ℂ) (hD : Summable (fun n => ‖D n‖ * ‖z‖ ^ n))
    (hU : Summable (fun n => ‖U n‖ * ‖z‖ ^ n)) :
    (∑' n : ℕ, (((n+1 : ℕ) : ℂ) * z ^ n) • U (n+1)) =
      v5ODESum D z * v5ODESum U z := by
  have hDn : Summable (fun n => ‖z ^ n • D n‖) := by
    simpa only [norm_smul, norm_pow, mul_comm] using hD
  have hUn : Summable (fun n => ‖z ^ n • U n‖) := by
    simpa only [norm_smul, norm_pow, mul_comm] using hU
  unfold v5ODESum
  rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hDn hUn]
  apply tsum_congr
  intro n
  calc
    (((n+1 : ℕ) : ℂ) * z ^ n) • U (n+1) = z ^ n •
        (((n+1 : ℕ) : ℂ) • U (n+1)) := by rw [smul_smul, mul_comm]
    _ = ∑ j ∈ Finset.range (n+1), z ^ n • (D j * U (n-j)) := by
      rw [hrec, Finset.smul_sum]
    _ = ∑ j ∈ Finset.range (n+1), (z ^ j • D j) * (z ^ (n-j) • U (n-j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      rw [smul_mul_assoc, mul_smul_comm, smul_smul, ← pow_add, Nat.add_sub_of_le hjn]

/-- The summed coefficient recursion solves the actual analytic ODE. -/
theorem v5_ode_sum_hasDerivAt
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (D U : ℕ → A)
    (hrec : ∀ n : ℕ, ((n + 1 : ℕ) : ℂ) • U (n + 1) =
      ∑ j ∈ Finset.range (n + 1), D j * U (n - j))
    (hD : ∀ s : ℝ, 0 ≤ s → Summable (fun n => ‖D n‖ * s ^ n))
    (hU : ∀ s : ℝ, 0 ≤ s → Summable (fun n => ‖U n‖ * s ^ n)) (z : ℂ) :
    HasDerivAt (v5ODESum U) (v5ODESum D z * v5ODESum U z) z := by
  rw [← v5_ode_derivative_series_eq_product D U hrec z
    (hD ‖z‖ (norm_nonneg _)) (hU ‖z‖ (norm_nonneg _))]
  exact v5_ode_sum_hasDerivAt_series D U hrec hD hU z

/-- Identification of the coefficient sum with the actual complex exponential. -/
theorem v5_exponential_coeff_hasSum
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (B : A) (c z : ℂ) :
    HasSum (fun n : ℕ => z ^ n • ((c ^ n / (n.factorial : ℂ)) • B))
      (Complex.exp (c*z) • B) := by
  rw [Complex.exp_eq_exp_ℂ]
  convert (NormedSpace.expSeries_div_hasSum_exp ℂ (c*z)).smul_const B using 1
  funext n
  rw [smul_smul, mul_pow]
  congr 1
  ring

theorem v5_finite_exponential_sum_eq
    {A ι : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (J : Finset ι) (B : ι → A) (c : ι → ℂ) (z : ℂ) :
    v5ODESum (fun n => ∑ j ∈ J, (c j ^ n / (n.factorial : ℂ)) • B j) z =
      ∑ j ∈ J, Complex.exp (c j*z) • B j := by
  have h := hasSum_sum (fun j (_ : j ∈ J) => v5_exponential_coeff_hasSum (B j) (c j) z)
  convert h.tsum_eq using 1
  unfold v5ODESum
  congr 1
  funext n
  exact Finset.smul_sum

/-- The constructed sum solves the ODE with the stated finite exponential
coefficient function, not merely a formal or unnamed coefficient sum. -/
theorem v5_finite_exponential_ode_hasDerivAt
    {A ι : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (J : Finset ι) (B : ι → A) (c : ι → ℂ) (U0 : A) (z : ℂ) :
    let D := fun n : ℕ => ∑ j ∈ J, (c j ^ n / (n.factorial : ℂ)) • B j
    let U := v5ODECoefficients D U0
    HasDerivAt (v5ODESum U)
      ((∑ j ∈ J, Complex.exp (c j*z) • B j) * v5ODESum U z) z := by
  dsimp only
  rw [← v5_finite_exponential_sum_eq J B c z]
  apply v5_ode_sum_hasDerivAt
  · exact v5ODECoefficients_recurrence _ _
  · intro s hs
    exact v5_finite_exponential_coeff_summable J B c s hs
  · intro r hr
    apply v5_ode_convolution_summable _ _ (v5ODECoefficients_recurrence _ _) _ r hr
    intro s hs
    exact v5_finite_exponential_coeff_summable J B c s hs.le

@[simp] theorem v5ODESum_zero
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] (U : ℕ → A) :
    v5ODESum U 0 = U 0 := by
  unfold v5ODESum
  rw [tsum_eq_single 0]
  · simp only [pow_zero, one_smul]
  · intro n hn
    simp only [zero_pow hn, zero_smul]

/-- Global complex differentiable existence, with arbitrary initial value,
for the finite exponential-sum left ODE in a complete normed algebra. -/
theorem v5_finite_exponential_ode_exists
    {A ι : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (J : Finset ι) (B : ι → A) (c : ι → ℂ) (U0 : A) :
    ∃ f : ℂ → A, f 0 = U0 ∧ ∀ z : ℂ,
      HasDerivAt f ((∑ j ∈ J, Complex.exp (c j*z) • B j) * f z) z := by
  refine ⟨v5ODESum (v5ODECoefficients
    (fun n => ∑ j ∈ J, (c j ^ n / (n.factorial : ℂ)) • B j) U0), ?_, ?_⟩
  · rw [v5ODESum_zero, v5ODECoefficients_zero]
  · intro z
    exact v5_finite_exponential_ode_hasDerivAt J B c U0 z

end StrictEUnit
#print axioms StrictEUnit.v5_ode_derivative_weights_summable
#print axioms StrictEUnit.v5_ode_terms_summable
#print axioms StrictEUnit.v5_ode_sum_hasDerivAt_series
#print axioms StrictEUnit.v5_ode_derivative_series_eq_product
#print axioms StrictEUnit.v5_ode_sum_hasDerivAt
#print axioms StrictEUnit.v5_exponential_coeff_hasSum
#print axioms StrictEUnit.v5_finite_exponential_sum_eq
#print axioms StrictEUnit.v5_finite_exponential_ode_hasDerivAt
#print axioms StrictEUnit.v5ODESum_zero
#print axioms StrictEUnit.v5_finite_exponential_ode_exists
