import V5ODEConvolution
import Mathlib.Analysis.Complex.Basic

noncomputable section
namespace StrictEUnit

/-- The normalized Taylor recursion for a left linear ODE, with arbitrary initial value. -/
def v5ODECoefficients {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (D : ℕ → A) (U0 : A) : ℕ → A
  | 0 => U0
  | n + 1 => ((n + 1 : ℕ) : ℂ)⁻¹ •
      ∑ j ∈ (Finset.range (n + 1)).attach,
        D j.1 * v5ODECoefficients D U0 (n - j.1)
termination_by n => n

@[simp] theorem v5ODECoefficients_zero {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (D : ℕ → A) (U0 : A) : v5ODECoefficients D U0 0 = U0 := by
  rw [v5ODECoefficients]

theorem v5ODECoefficients_recurrence {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (D : ℕ → A) (U0 : A) (n : ℕ) :
    ((n + 1 : ℕ) : ℂ) • v5ODECoefficients D U0 (n + 1) =
      ∑ j ∈ Finset.range (n + 1), D j * v5ODECoefficients D U0 (n - j) := by
  rw [v5ODECoefficients]
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [smul_inv_smul₀ hn]
  exact Finset.sum_attach (Finset.range (n + 1)) (fun j : ℕ => D j * v5ODECoefficients D U0 (n - j))

/-- A single exponential's algebra-valued Taylor coefficients are absolutely
summable at every radius. -/
theorem v5_exponential_coeff_summable
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (B : A) (c : ℂ) (s : ℝ) :
    Summable (fun n : ℕ => ‖(c ^ n / (n.factorial : ℂ)) • B‖ * s ^ n) := by
  convert (Real.summable_pow_div_factorial (‖c‖ * s)).mul_left ‖B‖ using 1
  ext n
  rw [norm_smul, norm_div, norm_pow, Complex.norm_natCast, mul_pow]
  ring

/-- Finite exponential sums have absolutely summable Taylor coefficients at
all nonnegative radii, without requiring a commutative coefficient algebra. -/
theorem v5_finite_exponential_coeff_summable
    {A ι : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (J : Finset ι) (B : ι → A) (c : ι → ℂ) (s : ℝ) (hs : 0 ≤ s) :
    Summable (fun n : ℕ => ‖∑ j ∈ J, (c j ^ n / (n.factorial : ℂ)) • B j‖ * s ^ n) := by
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hs n)) _
    (summable_sum (fun j (_ : j ∈ J) => v5_exponential_coeff_summable (B j) (c j) s))
  intro n
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (norm_sum_le _ _) (pow_nonneg hs n)

/-- The constructed recursion is the unique coefficient sequence with the
specified initial value and left ODE convolution recurrence. -/
theorem v5ODECoefficients_unique
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (D U : ℕ → A) (U0 : A) (hzero : U 0 = U0)
    (hrec : ∀ n : ℕ, ((n + 1 : ℕ) : ℂ) • U (n + 1) =
      ∑ j ∈ Finset.range (n + 1), D j * U (n - j)) :
    U = v5ODECoefficients D U0 := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa using hzero
    | succ n =>
      have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      have he : ((n+1 : ℕ) : ℂ) • U (n+1) =
          ((n+1 : ℕ) : ℂ) • v5ODECoefficients D U0 (n+1) := by
        rw [hrec, v5ODECoefficients_recurrence]
        apply Finset.sum_congr rfl
        intro j hj
        rw [ih (n-j) (Nat.lt_succ_of_le (Nat.sub_le _ _))]
      have hh := congrArg (fun x : A => ((n+1 : ℕ) : ℂ)⁻¹ • x) he
      simpa only [inv_smul_smul₀ hn] using hh

/-- Constructed solution coefficients for any entire coefficient sequence
have infinite radius, not merely a conditional supplied solution. -/
theorem v5ODECoefficients_radius_eq_top
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (D : ℕ → A) (U0 : A)
    (hD : ∀ s : ℝ, 0 < s → Summable (fun j => ‖D j‖ * s ^ j)) :
    FormalMultilinearSeries.radius
      (fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (v5ODECoefficients D U0 n)) = ⊤ :=
  v5_ode_convolution_radius_eq_top D (v5ODECoefficients D U0)
    (v5ODECoefficients_recurrence D U0) hD

/-- In particular, the actual recursively constructed coefficients for a
finite exponential-sum ODE have infinite radius. -/
theorem v5_finite_exponential_ode_radius_eq_top
    {A ι : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (J : Finset ι) (B : ι → A) (c : ι → ℂ) (U0 : A) :
    FormalMultilinearSeries.radius
      (fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n)
        (v5ODECoefficients (fun m => ∑ j ∈ J, (c j ^ m / (m.factorial : ℂ)) • B j) U0 n)) = ⊤ := by
  apply v5ODECoefficients_radius_eq_top
  intro s hs
  exact v5_finite_exponential_coeff_summable J B c s hs.le

end StrictEUnit
#print axioms StrictEUnit.v5ODECoefficients_zero
#print axioms StrictEUnit.v5ODECoefficients_recurrence
#print axioms StrictEUnit.v5_exponential_coeff_summable
#print axioms StrictEUnit.v5_finite_exponential_coeff_summable
#print axioms StrictEUnit.v5ODECoefficients_unique
#print axioms StrictEUnit.v5ODECoefficients_radius_eq_top
#print axioms StrictEUnit.v5_finite_exponential_ode_radius_eq_top
