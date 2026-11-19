import Stage26ODERecurrenceCoefficients

noncomputable section
open scoped BigOperators
namespace StrictEUnit
open Polynomial
variable {K : Type*} [Field K]

/-- Finite delta expansion of each coefficient of the recurrence symbol. -/
theorem stage26_odeSymbolScalar_delta (p : ℕ → Polynomial K) (D i j : ℕ) :
    stage26_odeSymbolScalar p D i j =
      ∑ k ∈ Finset.range (D + 1), if j = D + i - k then (p i).coeff k else 0 := by
  classical
  unfold stage26_odeSymbolScalar
  split_ifs with h
  · symm
    rw [Finset.sum_eq_single (D + i - j)]
    · rw [if_pos (by omega)]
    · intro k hk hne
      rw [if_neg (by have := Finset.mem_range.mp hk; omega)]
    · intro hn
      exact False.elim (hn (Finset.mem_range.mpr (by omega)))
  · symm
    apply Finset.sum_eq_zero
    intro k hk
    rw [if_neg (by have := Finset.mem_range.mp hk; omega)]

/-- Regrouping by offset is an exact finite-sum identity. -/
theorem stage26_odeSymbolScalar_sum (p : ℕ → Polynomial K) (N D i : ℕ)
    (hi : i < N) (f : ℕ → K) :
    ∑ j ∈ Finset.range (D + N), stage26_odeSymbolScalar p D i j * f j =
      ∑ k ∈ Finset.range (D + 1), (p i).coeff k * f (D + i - k) := by
  classical
  simp_rw [stage26_odeSymbolScalar_delta, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_eq_single (D + i - k)]
  · simp
  · intro j hj hne
    simp [hne]
  · intro hn
    exact False.elim (hn (Finset.mem_range.mpr (by omega)))

/-- Every solution of the actual formal polynomial ODE satisfies its computed
polynomial recurrence. No characteristic-zero assumption is needed for this
identity or for nonvanishing of the symbol. -/
theorem stage26_ode_recurrence_identity (p : ℕ → Polynomial K) (N D : ℕ)
    (x : PowerSeries K) (hdeg : ∀ i < N, (p i).natDegree ≤ D)
    (hode : ∑ i ∈ Finset.range N,
      (p i : PowerSeries K) * ((PowerSeries.derivative K)^[i] x) = 0) (n : ℕ) :
    ∑ j ∈ Finset.range (D + N), (stage26_odeSymbol p N D j).eval (n : K) *
      PowerSeries.coeff K (n + j) x = 0 := by
  simp only [stage26_odeSymbol, eval_finset_sum, eval_mul, eval_C, Finset.sum_mul]
  rw [Finset.sum_comm]
  have h := stage26_ode_coefficient_identity p N D x hdeg hode n
  convert h using 1
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [mul_assoc] using stage26_odeSymbolScalar_sum p N D i
    (Finset.mem_range.mp hi)
    (fun j => (stage26_shiftedFalling j i).eval (n : K) * PowerSeries.coeff K (n + j) x)

/-- A nonzero formal polynomial differential relation produces a genuine
nonzero polynomial recurrence. The recurrence holds at every n because D
absorbs all backwards shifts. -/
theorem stage26_nonzero_ode_has_recurrence (p : ℕ → Polynomial K) (N D : ℕ)
    (x : PowerSeries K) (hdeg : ∀ i < N, (p i).natDegree ≤ D)
    (hne : ∃ i < N, p i ≠ 0)
    (hode : ∑ i ∈ Finset.range N,
      (p i : PowerSeries K) * ((PowerSeries.derivative K)^[i] x) = 0) :
    ∃ r : ℕ, ∃ q : Fin (r + 1) → Polynomial K,
      (∃ j, q j ≠ 0) ∧ ∀ n : ℕ,
        ∑ j, (q j).eval (n : K) * PowerSeries.coeff K (n + j.val) x = 0 := by
  have hN : 0 < N := by obtain ⟨i, hi, _⟩ := hne; omega
  have hsize : D + N = (D + N - 1) + 1 := by omega
  refine ⟨D + N - 1, fun j => stage26_odeSymbol p N D j.val, ?_, ?_⟩
  · obtain ⟨j, hj, hq⟩ := stage26_odeSymbol_nonzero p N D hdeg hne
    exact ⟨⟨j, by omega⟩, hq⟩
  · intro n
    dsimp only
    rw [Fin.sum_univ_eq_sum_range
      (fun j => (stage26_odeSymbol p N D j).eval (n : K) * PowerSeries.coeff K (n + j) x)]
    simpa only [← hsize] using stage26_ode_recurrence_identity p N D x hdeg hode n

/-- Finite-tuple interface: every nonzero polynomial formal ODE gives a genuine
polynomial recurrence, without requiring a separate degree-bound witness. -/
theorem stage26_finite_ode_has_recurrence (m : ℕ) (p : Fin (m + 1) → Polynomial K)
    (x : PowerSeries K) (hne : ∃ i, p i ≠ 0)
    (hode : ∑ i, (p i : PowerSeries K) *
      ((PowerSeries.derivative K)^[i.val] x) = 0) :
    ∃ r : ℕ, ∃ q : Fin (r + 1) → Polynomial K,
      (∃ j, q j ≠ 0) ∧ ∀ n : ℕ,
        ∑ j, (q j).eval (n : K) * PowerSeries.coeff K (n + j.val) x = 0 := by
  classical
  let P : ℕ → Polynomial K := fun i => if h : i < m + 1 then p ⟨i, h⟩ else 0
  let D := Finset.univ.sup (fun i : Fin (m + 1) => (p i).natDegree)
  have hP : ∀ i < m + 1, (P i).natDegree ≤ D := by
    intro i hi
    simp only [P, dif_pos hi]
    exact Finset.le_sup (f := fun j : Fin (m + 1) => (p j).natDegree) (Finset.mem_univ (⟨i, hi⟩ : Fin (m + 1)))
  have hneP : ∃ i < m + 1, P i ≠ 0 := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i.val, i.isLt, by simpa [P, i.isLt] using hi⟩
  have hodeP : ∑ i ∈ Finset.range (m + 1), (P i : PowerSeries K) *
      ((PowerSeries.derivative K)^[i] x) = 0 := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun i => (P i : PowerSeries K) * ((PowerSeries.derivative K)^[i] x))]
    simpa only [P, dif_pos (Fin.isLt _)] using hode
  exact stage26_nonzero_ode_has_recurrence P (m + 1) D x hP hneP hodeP

end StrictEUnit
