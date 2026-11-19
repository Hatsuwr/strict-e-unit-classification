import ClassExponentRationalityReduction
import Mathlib.RingTheory.Valuation.Integral

noncomputable section
namespace StrictEUnit
variable {K Γ₀ : Type*} [Field K] [CharZero K] [LinearOrderedCommGroupWithZero Γ₀]

/-- If all falling factors are valuation units, the whole numerator is a unit. -/
theorem fallingFactorial_valuation_one (v : Valuation K Γ₀) (a : K) (n : ℕ)
    (hu : ∀ j, j < n → v (a - (j : K)) = 1) :
    v ((descPochhammer K n).eval a) = 1 := by
  rw [descPochhammer_eval_eq_prod_range, map_prod]
  exact Finset.prod_eq_one (fun j hj => hu j (Finset.mem_range.mp hj))

/-- A local, non-circular denominator obstruction. For a place where every
falling factor is a unit, clearing the nth binomial coefficient requires at
least the full factorial valuation. No prime-density or rationality is assumed. -/
theorem binomial_denominator_valuation_le_factorial
    (v : Valuation K Γ₀) (a : K) (n d : ℕ)
    (hu : ∀ j, j < n → v (a - (j : K)) = 1)
    (hint : v ((d : K) * ((descPochhammer K n).eval a / (n.factorial : K))) ≤ 1) :
    v (d : K) ≤ v (n.factorial : K) := by
  let y := (d : K) * ((descPochhammer K n).eval a / (n.factorial : K))
  have he : (d : K) * (descPochhammer K n).eval a = (n.factorial : K) * y := by
    dsimp [y]
    field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)]
  have hv := congrArg v he
  rw [map_mul, fallingFactorial_valuation_one v a n hu, mul_one, map_mul] at hv
  rw [hv]
  simpa only [mul_one] using mul_le_mul_left' hint (v (n.factorial : K))

/-- Actual algebraic integrality gives the valuation hypothesis, for any
nonarchimedean valuation; no local-integrality assumption is added. -/
theorem valuation_le_one_of_integer_integral (v : Valuation K Γ₀) (x : K)
    (hx : IsIntegral ℤ x) : v x ≤ 1 := by
  exact (Valuation.integer.integers v).mem_of_integral (hx.tower_top : IsIntegral v.integer x)

theorem binomial_integral_denominator_valuation_le_factorial
    (v : Valuation K Γ₀) (a : K) (n d : ℕ)
    (hu : ∀ j, j < n → v (a - (j : K)) = 1)
    (hint : IsIntegral ℤ ((d : K) * ((descPochhammer K n).eval a / (n.factorial : K)))) :
    v (d : K) ≤ v (n.factorial : K) :=
  binomial_denominator_valuation_le_factorial v a n d hu
    (valuation_le_one_of_integer_integral v _ hint)

/-- The already-proved joint binomial arithmetic supplies the SAME small
integer denominator with all applicable local factorial lower bounds. -/
theorem jointBinomialPrefixDenominators_local_obstruction {ι : Type*}
    (rho : ι → K) (h : JointBinomialPrefixDenominators rho) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ C^(N+1) ∧
      ∀ (v : Valuation K Γ₀) (i : ι) (n : ℕ), n ≤ N →
      (∀ j, j < n → v (rho i - (j : K)) = 1) → v (d : K) ≤ v (n.factorial : K) := by
  obtain ⟨C, hC, hD⟩ := h
  refine ⟨C, hC, ?_⟩
  intro N
  obtain ⟨d, hd, hb, hi⟩ := hD N
  exact ⟨d, hd, hb, fun v i n hn hu =>
    binomial_integral_denominator_valuation_le_factorial v (rho i) n d hu (hi n hn i)⟩

end StrictEUnit
end
