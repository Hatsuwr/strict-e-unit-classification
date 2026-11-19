import Stage26ODERecurrence
import Stage41StrictSeriesRealization
import Mathlib.Algebra.Polynomial.Monic

/-! NEW SOURCE-ONLY, UNCOMPILED. Remove factorial denominators from the actual
Stage26 recurrence. This is a polynomial recurrence for the ORIGINAL a_n,
not a G/E-operator theorem or arithmetic local-basis existence result. -/
noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- The interval product from j+1 to j+length, reindexed by Finset.range. -/
def borelFactorialMultiplier (j length : ℕ) : Polynomial K :=
  ∏ s ∈ Finset.range length, (Polynomial.X + Polynomial.C ((j+s+1 : ℕ) : K))

theorem borelFactorialMultiplier_zero (j : ℕ) :
    borelFactorialMultiplier (K := K) j 0 = 1 := by
  simp only [borelFactorialMultiplier, Finset.range_zero, Finset.prod_empty]

theorem borelFactorialMultiplier_succ (j length : ℕ) :
    borelFactorialMultiplier (K := K) j (length+1) =
      borelFactorialMultiplier j length * (Polynomial.X + Polynomial.C ((j+length+1 : ℕ) : K)) := by
  exact Finset.prod_range_succ _ _

theorem borelFactorialMultiplier_monic (j length : ℕ) :
    (borelFactorialMultiplier (K := K) j length).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro s hs
  exact Polynomial.monic_X_add_C _

theorem borelFactorialMultiplier_ne_zero (j length : ℕ) :
    borelFactorialMultiplier (K := K) j length ≠ 0 :=
  (borelFactorialMultiplier_monic j length).ne_zero

/-- Exact factorial identity, including length zero. -/
theorem borelFactorialMultiplier_eval_mul_factorial (n j length : ℕ) :
    ((n+j).factorial : K) * (borelFactorialMultiplier j length).eval (n : K) =
      ((n+j+length).factorial : K) := by
  induction length with
  | zero => rw [borelFactorialMultiplier_zero, Polynomial.eval_one, mul_one, Nat.add_zero]
  | succ length ih =>
    rw [borelFactorialMultiplier_succ, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C, ← mul_assoc, ih]
    have ht : n+j+(length+1) = (n+j+length)+1 := by omega
    rw [ht, Nat.factorial_succ, Nat.cast_mul]
    push_cast
    ring

/-- At width r the extra factor is exactly (n+r)!/(n+j)!. -/
theorem borelFactorialMultiplier_eval_ratio (n r : ℕ) (j : Fin (r+1)) :
    (borelFactorialMultiplier j.val (r-j.val)).eval (n : K) =
      ((n+r).factorial : K) / ((n+j.val).factorial : K) := by
  have hj : ((n+j.val).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  apply (eq_div_iff hj).mpr
  have hsum : n+j.val+(r-j.val) = n+r := by omega
  simpa only [hsum, mul_comm] using
    borelFactorialMultiplier_eval_mul_factorial (K := K) n j.val (r-j.val)

/-- Clear every factorial with one common multiplier (n+r)!, preserving a
nonzero tuple. No bound or eventual-index hypothesis is introduced. -/
theorem borel_recurrence_clear_factorials (a : ℕ → K) (r : ℕ)
    (q : Fin (r+1) → Polynomial K) (hq : ∃ j, q j ≠ 0)
    (hrec : ∀ n : ℕ, (∑ j, (q j).eval (n : K) *
      (a (n+j.val) / ((n+j.val).factorial : K))) = 0) :
    let Q := fun j : Fin (r+1) => q j * borelFactorialMultiplier j.val (r-j.val)
    (∃ j, Q j ≠ 0) ∧ ∀ n : ℕ, (∑ j, (Q j).eval (n : K) * a (n+j.val)) = 0 := by
  dsimp only
  constructor
  · obtain ⟨j, hj⟩ := hq
    exact ⟨j, mul_ne_zero hj (borelFactorialMultiplier_ne_zero j.val (r-j.val))⟩
  · intro n
    calc
      (∑ j, (q j * borelFactorialMultiplier j.val (r-j.val)).eval (n : K) * a (n+j.val)) =
          ((n+r).factorial : K) *
            (∑ j, (q j).eval (n : K) * (a (n+j.val) / ((n+j.val).factorial : K))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Polynomial.eval_mul, borelFactorialMultiplier_eval_ratio]
        ring
      _ = 0 := by rw [hrec, mul_zero]

/-- The literal factorial-series ODE yields a polynomial recurrence for a_n,
not merely for its ordinary Taylor coefficients a_n/n!. -/
theorem factorialSeries_ode_original_coefficients_recurrence
    (a : ℕ → K) (m : ℕ) (p : Fin (m+1) → Polynomial K)
    (hp : ∃ i, p i ≠ 0)
    (hode : (∑ i, (p i : PowerSeries K) *
      (PowerSeries.derivative K : PowerSeries K → PowerSeries K)^[i.val]
        (PowerSeries.mk (fun n => a n / (n.factorial : K)))) = 0) :
    ∃ r : ℕ, ∃ Q : Fin (r+1) → Polynomial K,
      (∃ j, Q j ≠ 0) ∧ ∀ n : ℕ, (∑ j, (Q j).eval (n : K) * a (n+j.val)) = 0 := by
  obtain ⟨r, q, hq, hrec⟩ := stage26_finite_ode_has_recurrence m p
    (PowerSeries.mk (fun n => a n / (n.factorial : K))) hp hode
  have hrec' : ∀ n : ℕ, (∑ j, (q j).eval (n : K) *
      (a (n+j.val) / ((n+j.val).factorial : K))) = 0 := by
    intro n
    simpa only [PowerSeries.coeff_mk] using hrec n
  exact ⟨r, fun j => q j * borelFactorialMultiplier j.val (r-j.val),
    borel_recurrence_clear_factorials a r q hq hrec'⟩

/-- Stage41 specialization uses only its genuine ODE half. Arithmetic bounds
remain unchanged and are not used to assert a stronger operator theorem. -/
theorem stage41_original_coefficients_polynomial_recurrence
    (a : ℕ → AlgebraicComplex) (ha : Stage41IsStrictESeries a) :
    ∃ r : ℕ, ∃ Q : Fin (r+1) → Polynomial AlgebraicComplex,
      (∃ j, Q j ≠ 0) ∧ ∀ n : ℕ,
        (∑ j, (Q j).eval (n : AlgebraicComplex) * a (n+j.val)) = 0 := by
  obtain ⟨m, p, hp, hode⟩ := ha.2
  exact factorialSeries_ode_original_coefficients_recurrence a m p hp hode

end StrictEUnit
end
