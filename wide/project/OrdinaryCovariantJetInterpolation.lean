import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! New reconstruction, not recovered historical source.
The covariant jet map on polynomial rows is triangular in their ordinary
coefficients, with nonzero diagonal n!. Correct one jet at a time by adding
a degree-n monomial. No fundamental matrix or prescribed solution is assumed. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators
namespace StrictEUnit

variable {K : Type*} [Field K] {r : ℕ}

/-- Ordinary covariant derivative of a power-series row. -/
def ordinaryCovariantRow (M : Fin r → Fin r → PowerSeries K)
    (u : Fin r → PowerSeries K) : Fin r → PowerSeries K :=
  fun j => PowerSeries.derivative K (u j) + ∑ i, u i * M i j

theorem ordinaryCovariantRow_add (M : Fin r → Fin r → PowerSeries K)
    (u w : Fin r → PowerSeries K) :
    ordinaryCovariantRow M (u + w) = ordinaryCovariantRow M u + ordinaryCovariantRow M w := by
  funext j
  simp only [ordinaryCovariantRow, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  ring

theorem ordinaryCovariantRow_iterate_add (M : Fin r → Fin r → PowerSeries K)
    (u w : Fin r → PowerSeries K) (n : ℕ) :
    (ordinaryCovariantRow M)^[n] (u + w) =
      (ordinaryCovariantRow M)^[n] u + (ordinaryCovariantRow M)^[n] w := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply', ih, ordinaryCovariantRow_add]

private theorem ordinaryJet_coeff_mul_zero
    (f g : PowerSeries K) (n : ℕ)
    (hf : ∀ k, k ≤ n → PowerSeries.coeff K k f = 0) :
    PowerSeries.coeff K n (f * g) = 0 := by
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨a, b⟩ hab
  have hab' : a + b = n := Finset.mem_antidiagonal.mp hab
  rw [hf a (by omega), zero_mul]

/-- If all row coefficients through n vanish, the connection term contributes
nothing to coefficient n; only ordinary differentiation remains. -/
theorem ordinaryCovariantRow_coeff_of_vanishing
    (M : Fin r → Fin r → PowerSeries K) (u : Fin r → PowerSeries K) (n : ℕ)
    (hu : ∀ k, k ≤ n → ∀ j, PowerSeries.coeff K k (u j) = 0) (j : Fin r) :
    PowerSeries.coeff K n (ordinaryCovariantRow M u j) =
      PowerSeries.coeff K (n + 1) (u j) * (n + 1 : K) := by
  have hz : ∀ i, PowerSeries.coeff K n (u i * M i j) = 0 := by
    intro i
    exact ordinaryJet_coeff_mul_zero (u i) (M i j) n (fun k hk => hu k hk i)
  simp only [ordinaryCovariantRow, map_add, map_sum, PowerSeries.coeff_derivative,
    hz, Finset.sum_const_zero, add_zero]

/-- The leading covariant jet of a row vanishing to order n is exactly n!
times its nth ordinary coefficient. -/
theorem ordinaryCovariantRow_iterate_leading
    (M : Fin r → Fin r → PowerSeries K) (n : ℕ) (u : Fin r → PowerSeries K)
    (hu : ∀ k, k < n → ∀ j, PowerSeries.coeff K k (u j) = 0) (j : Fin r) :
    PowerSeries.coeff K 0 ((ordinaryCovariantRow M)^[n] u j) =
      (Nat.factorial n : K) * PowerSeries.coeff K n (u j) := by
  induction n generalizing u with
  | zero => simp only [Function.iterate_zero_apply, Nat.factorial_zero, Nat.cast_one, one_mul]
  | succ n ih =>
    have hdu : ∀ k, k < n → ∀ j,
        PowerSeries.coeff K k (ordinaryCovariantRow M u j) = 0 := by
      intro k hk j
      rw [ordinaryCovariantRow_coeff_of_vanishing M u k
        (fun a ha l => hu a (by omega) l) j]
      rw [hu (k + 1) (by omega) j, zero_mul]
    rw [Function.iterate_succ_apply, ih (ordinaryCovariantRow M u) hdu]
    rw [ordinaryCovariantRow_coeff_of_vanishing M u n
      (fun k hk l => hu k (by omega) l) j]
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring

/-- Actual polynomial rows realize arbitrary finite covariant jets. The proof
successively adjusts degree n using the invertible scalar n!, leaving all
previous jets fixed. -/
theorem exists_polynomial_covariant_jets [CharZero K]
    (M : Fin r → Fin r → PowerSeries K) (v : ℕ → Fin r → K) (n : ℕ) :
    ∃ p : Fin r → Polynomial K, ∀ i, i < n → ∀ j,
      PowerSeries.coeff K 0
        ((ordinaryCovariantRow M)^[i] (fun j => (p j : PowerSeries K)) j) = v i j := by
  induction n with
  | zero =>
    refine ⟨fun _ => 0, ?_⟩
    intro i hi
    omega
  | succ n ih =>
    obtain ⟨p, hp⟩ := ih
    let u : Fin r → PowerSeries K := fun j => (p j : PowerSeries K)
    let a : Fin r → K := fun j => (Nat.factorial n : K)⁻¹ *
      (v n j - PowerSeries.coeff K 0 ((ordinaryCovariantRow M)^[n] u j))
    let d : Fin r → Polynomial K := fun j => Polynomial.monomial n (a j)
    let w : Fin r → PowerSeries K := fun j => (d j : PowerSeries K)
    have hwlow : ∀ k, k < n → ∀ j, PowerSeries.coeff K k (w j) = 0 := by
      intro k hk j
      simp only [w, d, Polynomial.coe_monomial, PowerSeries.coeff_monomial,
        if_neg (Nat.ne_of_lt hk)]
    have hwtop : ∀ j, PowerSeries.coeff K n (w j) = a j := by
      intro j
      simp only [w, d, Polynomial.coe_monomial, PowerSeries.coeff_monomial_same]
    refine ⟨fun j => p j + d j, ?_⟩
    intro i hi j
    have hrow : (fun j => ((p j + d j : Polynomial K) : PowerSeries K)) = u + w := by
      funext l
      simp only [Polynomial.coe_add, Pi.add_apply, u, w]
    rw [hrow, ordinaryCovariantRow_iterate_add, Pi.add_apply, map_add]
    by_cases hin : i < n
    · have hzero : PowerSeries.coeff K 0 ((ordinaryCovariantRow M)^[i] w j) = 0 := by
        rw [ordinaryCovariantRow_iterate_leading M i w
          (fun k hk l => hwlow k (by omega) l) j, hwlow i hin j, mul_zero]
      rw [hzero, add_zero]
      exact hp i hin j
    · have hieq : i = n := by omega
      subst i
      rw [ordinaryCovariantRow_iterate_leading M n w hwlow j, hwtop j]
      have hn : (Nat.factorial n : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      dsimp only [a]
      rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]
      ring

end StrictEUnit
