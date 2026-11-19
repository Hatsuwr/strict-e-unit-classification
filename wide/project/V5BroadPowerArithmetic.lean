import Mathlib.NumberTheory.NumberField.House
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity

noncomputable section
namespace StrictEUnit
open scoped NumberField

/-- The usual broad arithmetic hypothesis over a fixed number field. -/
def V5BroadArithmetic {K : Type*} [Field K] [NumberField K] (a : ℕ → K) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℕ → ℕ, (∀ L, 0 < δ L) ∧
      (∀ L, (δ L : ℝ) ≤ C^(L+1) * (L.factorial : ℝ)^ε) ∧
      (∀ n, NumberField.house (a n) ≤ C^(n+1) * (n.factorial : ℝ)^ε) ∧
      (∀ L n, n ≤ L → IsIntegral ℤ ((δ L : K) * a n))

/-- Quantifying over positive integer powers removes real exponents from the
finite Padé cutoff estimates without strengthening the input. -/
theorem v5_broad_arithmetic_power_bounds {K : Type*} [Field K] [NumberField K]
    (a : ℕ → K) (ha : V5BroadArithmetic a) (p : ℕ) (hp : 0 < p) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℕ → ℕ, (∀ L, 0 < δ L) ∧
      (∀ L, (δ L : ℝ)^p ≤ C^(L+1) * (L.factorial : ℝ)) ∧
      (∀ n, NumberField.house (a n)^p ≤ C^(n+1) * (n.factorial : ℝ)) ∧
      (∀ L n, n ≤ L → IsIntegral ℤ ((δ L : K) * a n)) := by
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  obtain ⟨C,hC,δ,hδ,hδb,hab,hint⟩ := ha ((p:ℝ)⁻¹) (inv_pos.mpr hpR)
  have hfactor (n : ℕ) :
      (C^(n+1) * (n.factorial:ℝ)^((p:ℝ)⁻¹))^p = (C^p)^(n+1) * (n.factorial:ℝ) := by
    rw [mul_pow, ← Real.rpow_mul_natCast (by positivity), inv_mul_cancel₀ hpR.ne',
      Real.rpow_one, ← pow_mul, ← pow_mul, Nat.mul_comm (n+1) p]
  refine ⟨C^p, one_le_pow₀ hC, δ,hδ,?_,?_,hint⟩
  · intro L
    rw [← hfactor L]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (hδb L) _
  · intro n
    rw [← hfactor n]
    exact pow_le_pow_left₀ (NumberField.house_nonneg _) (hab n) _

/-- A fixed finite derivative shift costs only an exponential factor.
The same quantity bounds the derivative's rising coefficient multiplier. -/
theorem v5_factorial_shift_bound (L r : ℕ) :
    (L+r).factorial ≤ ((2:ℕ)^(r*(r+2)))^(L+1) * L.factorial := by
  have hL : L+1 ≤ (2 : ℕ)^(L+1) := Nat.le_of_lt (L+1).lt_two_pow_self
  have hr : r+1 ≤ (2 : ℕ)^(r+1) := Nat.le_of_lt (r+1).lt_two_pow_self
  have hshift : L+r ≤ (2 : ℕ)^((r+2)*(L+1)) := by
    calc
      _ ≤ (r+1)*(L+1) := by
        simp only [Nat.mul_add, Nat.mul_one, Nat.add_mul, Nat.two_mul]
        omega
      _ ≤ 2^(r+1)*2^(L+1) := Nat.mul_le_mul hr hL
      _ = 2^((r+1)+(L+1)) := (pow_add ..).symm
      _ ≤ _ := by
        apply Nat.pow_le_pow_right (by decide)
        simp only [Nat.mul_add, Nat.mul_one, Nat.add_mul, Nat.two_mul]
        omega
  calc
    _ = L.factorial * (L+1).ascFactorial r := (Nat.factorial_mul_ascFactorial ..).symm
    _ ≤ L.factorial * (L+r)^r := Nat.mul_le_mul_left _ (Nat.ascFactorial_le_pow_add L r)
    _ ≤ L.factorial * ((2:ℕ)^((r+2)*(L+1)))^r :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hshift _)
    _ = _ := by
      rw [mul_comm L.factorial, ← pow_mul, ← pow_mul]
      congr 2
      ring

#print axioms v5_broad_arithmetic_power_bounds
#print axioms v5_factorial_shift_bound
end StrictEUnit
end
