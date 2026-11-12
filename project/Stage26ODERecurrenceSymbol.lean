import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

/-! The coefficient-symbol transform of a polynomial differential operator.
The nonvanishing theorem is algebraic: it does not assume a recurrence or an
analytic solution. -/
noncomputable section
open scoped BigOperators
namespace StrictEUnit
open Polynomial
variable {K : Type*} [Field K]

/-- Falling factorial in the shifted coefficient index. -/
def stage26_shiftedFalling (j i : ℕ) : Polynomial K :=
  (descPochhammer K i).comp (X + C (j : K))

theorem stage26_shiftedFalling_degree (j i : ℕ) :
    (stage26_shiftedFalling (K := K) j i).natDegree = i := by
  rw [stage26_shiftedFalling, natDegree_comp, descPochhammer_natDegree,
    natDegree_X_add_C, Nat.mul_one]

theorem stage26_shiftedFalling_monic (j i : ℕ) :
    (stage26_shiftedFalling (K := K) j i).Monic :=
  (monic_descPochhammer K i).comp_X_add_C _

/-- Monic polynomials of consecutive degrees are linearly independent, in the
explicit finite-sum form needed for the differential-operator symbol. -/
theorem stage26_triangular_sum_eq_zero (b : ℕ → Polynomial K)
    (hb : ∀ i, (b i).natDegree = i) (hm : ∀ i, (b i).Monic)
    (c : ℕ → K) (N : ℕ)
    (h : ∑ i ∈ Finset.range N, C (c i) * b i = 0) :
    ∀ i < N, c i = 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hc : c N = 0 := by
      have hh := congrArg (fun p : Polynomial K => p.coeff N) h
      dsimp only at hh
      rw [Finset.sum_range_succ, coeff_add, coeff_C_mul] at hh
      have hz : (∑ i ∈ Finset.range N, C (c i) * b i).coeff N = 0 := by
        rw [finset_sum_coeff]
        apply Finset.sum_eq_zero
        intro i hi
        rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt, mul_zero]
        simpa [hb] using Finset.mem_range.mp hi
      have htop : (b N).coeff N = 1 := by simpa only [hb] using (hm N).coeff_natDegree
      rw [hz, htop, mul_one, zero_add, coeff_zero] at hh
      exact hh
    have hp : ∑ i ∈ Finset.range N, C (c i) * b i = 0 := by
      simpa [Finset.sum_range_succ, hc] using h
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact ih hp i hi
    · exact hc

/-- Scalar of derivative order i contributing to shifted sequence index j.
D bounds all polynomial exponents; the guard prevents truncated subtraction
from turning absent negative exponents into spurious constant terms. -/
def stage26_odeSymbolScalar (p : ℕ → Polynomial K) (D i j : ℕ) : K :=
  if j ≤ D + i ∧ D + i - j ≤ D then (p i).coeff (D + i - j) else 0

/-- The genuine polynomial recurrence symbol at offset j. -/
def stage26_odeSymbol (p : ℕ → Polynomial K) (N D j : ℕ) : Polynomial K :=
  ∑ i ∈ Finset.range N,
    C (stage26_odeSymbolScalar p D i j) * stage26_shiftedFalling j i

/-- No cancellation among derivative orders can make a symbol vanish unless
all its contributing polynomial coefficients vanish individually. -/
theorem stage26_odeSymbol_eq_zero_iff (p : ℕ → Polynomial K) (N D j : ℕ) :
    stage26_odeSymbol p N D j = 0 ↔
      ∀ i < N, stage26_odeSymbolScalar p D i j = 0 := by
  constructor
  · exact stage26_triangular_sum_eq_zero _ (stage26_shiftedFalling_degree j)
      (stage26_shiftedFalling_monic j) _ N
  · intro h
    apply Finset.sum_eq_zero
    intro i hi
    simp [h i (Finset.mem_range.mp hi)]

/-- A nonzero polynomial ODE has a genuinely nonzero recurrence symbol.
This closes the possible-cancellation issue rather than assuming it away. -/
theorem stage26_odeSymbol_nonzero (p : ℕ → Polynomial K) (N D : ℕ)
    (hdeg : ∀ i < N, (p i).natDegree ≤ D)
    (hne : ∃ i < N, p i ≠ 0) :
    ∃ j < D + N, stage26_odeSymbol p N D j ≠ 0 := by
  obtain ⟨i, hi, hp⟩ := hne
  let k := (p i).natDegree
  have hk : k ≤ D := hdeg i hi
  refine ⟨D + i - k, by omega, ?_⟩
  intro hz
  have h := (stage26_odeSymbol_eq_zero_iff p N D _).mp hz i hi
  have hsub : D + i - (D + i - k) = k := by omega
  have hguard : D + i - k ≤ D + i ∧ D + i - (D + i - k) ≤ D := by omega
  unfold stage26_odeSymbolScalar at h
  rw [if_pos hguard, hsub] at h
  exact (leadingCoeff_ne_zero.mpr hp) h

end StrictEUnit
