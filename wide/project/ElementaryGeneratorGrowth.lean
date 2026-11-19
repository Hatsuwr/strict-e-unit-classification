import RingExpressionGrowth

/-! Direct growth bounds for the elementary functions in the log-free
manuscript ring, and pullback of an explicitly bounded function under z^N.
No E-function arithmetic or determinant identity is assumed proved here. -/
noncomputable section
namespace StrictEUnit
variable {Ω : Type*}

/-- The actual complex coordinate has a polynomial bound. -/
theorem powerExponentialBound_coordinate (N : ℕ) (z : Ω → ℂ) :
    HasPowerExponentialBoundOn N z z := by
  apply powerExponentialBound_of_separate_constants N 1 z z 1 0 (by norm_num) le_rfl
  intro t ht
  simp only [pow_one, one_mul, zero_mul, Real.exp_zero, mul_one]
  linarith

/-- Coordinate inversion is bounded outside the unit disk. This is not
closure under inversion of arbitrary bounded functions. -/
theorem powerExponentialBound_coordinate_inv (N : ℕ) (z : Ω → ℂ) :
    HasPowerExponentialBoundOn N z (fun t => (z t)⁻¹) := by
  apply powerExponentialBound_of_separate_constants N 0 z (fun t => (z t)⁻¹)
    1 0 (by norm_num) le_rfl
  intro t ht
  simp only [pow_zero, one_mul, zero_mul, Real.exp_zero, norm_inv]
  exact inv_le_one_of_one_le₀ ht

/-- Powers are finite products in the proved growth subalgebra. -/
theorem powerExponentialBound_pow (N : ℕ) (z f : Ω → ℂ)
    (hf : HasPowerExponentialBoundOn N z f) (m : ℕ) :
    HasPowerExponentialBoundOn N z (fun t => f t ^ m) :=
  (powerExponentialBoundSubalgebra N z).pow_mem hf m

/-- Every integral power of the coordinate has the required exterior growth. -/
theorem powerExponentialBound_coordinate_zpow (N : ℕ) (z : Ω → ℂ) (m : ℤ) :
    HasPowerExponentialBoundOn N z (fun t => z t ^ m) := by
  cases m with
  | ofNat n =>
    simpa only [zpow_natCast] using
      powerExponentialBound_pow N z z (powerExponentialBound_coordinate N z) n
  | negSucc n =>
    simpa only [zpow_negSucc, inv_pow] using
      powerExponentialBound_pow N z (fun t => (z t)⁻¹)
        (powerExponentialBound_coordinate_inv N z) (n+1)

/-- Actual complex exponentials exp(a*z^N) have the stated growth. -/
theorem powerExponentialBound_exp_monomial (N : ℕ) (z : Ω → ℂ) (a : ℂ) :
    HasPowerExponentialBoundOn N z (fun t => Complex.exp (a * z t ^ N)) := by
  apply powerExponentialBound_of_separate_constants N 0 z _ 1 ‖a‖
    (by norm_num) (norm_nonneg _)
  intro t ht
  simp only [pow_zero, one_mul, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simpa only [norm_mul, norm_pow] using Complex.re_le_norm (a * z t ^ N)

/-- The explicit Laurent-monomial times exponential formula occurring in the
determinant inverse has a bound. Its equality with a determinant inverse is
not asserted by this growth-only theorem. -/
theorem powerExponentialBound_laurent_exp (N : ℕ) (z : Ω → ℂ)
    (c a : ℂ) (m : ℤ) :
    HasPowerExponentialBoundOn N z
      (fun t => c * z t ^ m * Complex.exp (a * z t ^ N)) :=
  powerExponentialBound_mul N z _ _
    (powerExponentialBound_mul N z _ _ (powerExponentialBound_const N z c)
      (powerExponentialBound_coordinate_zpow N z m))
    (powerExponentialBound_exp_monomial N z a)

/-- An actual exponential-type estimate pulls back along the actual power
map with the desired order N. The estimate for F is the explicit premise. -/
theorem powerExponentialBound_power_pullback (N : ℕ) (z : Ω → ℂ) (F : ℂ → ℂ)
    (C : ℝ) (hC : 0 < C)
    (hF : ∀ w : ℂ, ‖F w‖ ≤ C * Real.exp (C * ‖w‖)) :
    HasPowerExponentialBoundOn N z (fun t => F (z t ^ N)) := by
  refine ⟨C, hC, 0, fun t ht => ?_⟩
  simpa only [pow_zero, mul_one, norm_pow] using hF (z t ^ N)

end StrictEUnit
#print axioms StrictEUnit.powerExponentialBound_coordinate
#print axioms StrictEUnit.powerExponentialBound_coordinate_inv
#print axioms StrictEUnit.powerExponentialBound_pow
#print axioms StrictEUnit.powerExponentialBound_coordinate_zpow
#print axioms StrictEUnit.powerExponentialBound_exp_monomial
#print axioms StrictEUnit.powerExponentialBound_laurent_exp
#print axioms StrictEUnit.powerExponentialBound_power_pullback
