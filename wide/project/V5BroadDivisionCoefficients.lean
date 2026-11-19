import V5BroadActualData
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- Exact factorial coefficients of formal division by 1 - X. -/
def v5DivisionCoeff {K : Type*} [Ring K] (a : ℕ → K) : ℕ → K
  | 0 => a 0
  | n+1 => a (n+1) + (n+1 : K) * v5DivisionCoeff a n

theorem v5_divisionCoeff_map {K L : Type*} [Ring K] [Ring L]
    (φ : K →+* L) (a : ℕ → K) (n : ℕ) :
    φ (v5DivisionCoeff a n) = v5DivisionCoeff (fun j => φ (a j)) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [v5DivisionCoeff, ih]

theorem v5_divisionCoeff_normalized {K : Type*} [Field K] [CharZero K]
    (a : ℕ → K) (n : ℕ) :
    v5DivisionCoeff a n / (n.factorial : K) =
      ∑ j ∈ Finset.range (n+1), a j / (j.factorial : K) := by
  induction n with
  | zero => simp [v5DivisionCoeff]
  | succ n ih =>
    have hn : (n+1 : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hfac : (n.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    rw [v5DivisionCoeff, Finset.sum_range_succ, ← ih,
      Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
    ring

/-- The finite recurrence is exactly the formal quotient equation. -/
theorem v5_factorial_division_formal {K : Type*} [Field K] [CharZero K] (a : ℕ → K) :
    (1-PowerSeries.X : PowerSeries K) *
      PowerSeries.mk (fun n => v5DivisionCoeff a n / (n.factorial : K)) =
      PowerSeries.mk (fun n => a n / (n.factorial : K)) := by
  rw [sub_mul, one_mul]
  ext n
  cases n with
  | zero =>
    simp [v5DivisionCoeff]
  | succ n =>
    rw [map_sub, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
      PowerSeries.coeff_mk, v5_divisionCoeff_normalized, Finset.sum_range_succ,
      ← v5_divisionCoeff_normalized a n]
    ring

/-- A common positive integer for the original prefix also clears the
same prefix of the quotient, without enlarging the integer. -/
theorem v5_divisionCoeff_integral_prefix {K : Type*} [Field K] [CharZero K]
    (a : ℕ → K) (d N : ℕ)
    (hint : ∀ j ≤ N, IsIntegral ℤ ((d : K) * a j)) :
    ∀ j ≤ N, IsIntegral ℤ ((d : K) * v5DivisionCoeff a j) := by
  intro j
  induction j with
  | zero =>
    intro h
    simpa only [v5DivisionCoeff] using hint 0 h
  | succ j ih =>
    intro h
    have hj : j ≤ N := (Nat.le_succ j).trans h
    have hi : IsIntegral ℤ (j+1 : K) := by
      exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := K) (x := ((j+1 : ℕ) : ℤ)))
    have hp := (hint (j+1) h).add (hi.mul (ih hj))
    convert hp using 1
    simp only [v5DivisionCoeff]
    ring

/-- Apply this separately to each conjugate; no field map is applied to
an infinite complex sum. -/
theorem v5_divisionCoeff_tail_hasSum (a : ℕ → ℂ)
    (hzero : HasSum (fun j => a j / (j.factorial : ℂ)) 0) (n : ℕ) :
    HasSum (fun j => -(n.factorial : ℂ) *
      (a (j+(n+1)) / ((j+(n+1)).factorial : ℂ))) (v5DivisionCoeff a n) := by
  have ht := (hasSum_nat_add_iff' (f := fun j => a j / (j.factorial : ℂ)) (n+1)).mpr hzero
  have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have he : -(n.factorial : ℂ) * (0 - ∑ j ∈ Finset.range (n+1), a j / (j.factorial : ℂ)) =
      v5DivisionCoeff a n := by
    rw [zero_sub, neg_mul_neg, ← v5_divisionCoeff_normalized a n, mul_div_cancel₀ _ hn]
  simpa only [he] using ht.mul_left (-(n.factorial : ℂ))

#print axioms v5_factorial_division_formal
#print axioms v5_divisionCoeff_integral_prefix
#print axioms v5_divisionCoeff_tail_hasSum
end StrictEUnit
end
