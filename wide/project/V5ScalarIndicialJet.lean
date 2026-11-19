import Stage26ODERecurrence
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Bounds.Basic

noncomputable section
open scoped BigOperators
namespace StrictEUnit
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

/-- A nonzero polynomial has no natural-number roots beyond a finite cutoff. -/
theorem v5_polynomial_nat_eventually_ne (q : Polynomial K) (hq : q ≠ 0) :
    ∃ c : ℕ, ∀ n ≥ c, q.eval (n : K) ≠ 0 := by
  classical
  have hf : Set.Finite {n : ℕ | q.eval (n : K) = 0} :=
    (q.finite_setOf_isRoot hq).preimage (Nat.cast_injective.injOn)
  obtain ⟨c, hc⟩ := hf.bddAbove
  refine ⟨c+1, ?_⟩
  intro n hn hz
  have := hc hz
  omega

/-- The last nonzero grouped ODE symbol determines a genuinely triangular
recurrence, with a nonzero diagonal after one uniform cutoff. -/
theorem v5_scalar_indicial_recurrence (p : ℕ → Polynomial K) (N D : ℕ)
    (hdeg : ∀ i < N, (p i).natDegree ≤ D) (hne : ∃ i < N, p i ≠ 0) :
    ∃ h c : ℕ, h < D+N ∧ stage26_odeSymbol p N D h ≠ 0 ∧
      (∀ j, h < j → stage26_odeSymbol p N D j = 0) ∧
      (∀ n ≥ c, (stage26_odeSymbol p N D h).eval (n : K) ≠ 0) ∧
      ∀ x : PowerSeries K,
        (∑ i ∈ Finset.range N, (p i : PowerSeries K) *
          ((PowerSeries.derivative K)^[i] x) = 0) →
        ∀ n : ℕ, ∑ j ∈ Finset.range (h+1),
          (stage26_odeSymbol p N D j).eval (n : K) *
            PowerSeries.coeff K (n+j) x = 0 := by
  classical
  let S := (Finset.range (D+N)).filter (fun j => stage26_odeSymbol p N D j ≠ 0)
  have hs : S.Nonempty := by
    obtain ⟨j,hj,hq⟩ := stage26_odeSymbol_nonzero p N D hdeg hne
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hq⟩⟩
  let h := S.max' hs
  have hh := Finset.mem_filter.mp (S.max'_mem hs)
  have hlt : h < D+N := Finset.mem_range.mp hh.1
  have hnon : stage26_odeSymbol p N D h ≠ 0 := hh.2
  have hzero : ∀ j, h < j → stage26_odeSymbol p N D j = 0 := by
    intro j hj
    by_cases hbound : j < D+N
    · by_contra hn
      have hmem : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hbound, hn⟩
      have hle := S.le_max' j hmem
      omega
    · apply (stage26_odeSymbol_eq_zero_iff p N D j).mpr
      intro i hi
      simp only [stage26_odeSymbolScalar]
      rw [if_neg (by omega)]
  obtain ⟨c,hc⟩ := v5_polynomial_nat_eventually_ne _ hnon
  refine ⟨h,c,hlt,hnon,hzero,hc,?_⟩
  intro x hx n
  have heq := stage26_ode_recurrence_identity p N D x hdeg hx n
  rw [← heq]
  apply Finset.sum_subset (Finset.range_mono (by omega : h+1 ≤ D+N))
  intro j hj hjnot
  have hgreater : h < j := by
    have : ¬ j < h+1 := by simpa only [Finset.mem_range] using hjnot
    omega
  simp [hzero j hgreater]

omit [CharZero K]

/-- The scalar ODE operator, before taking any coefficients. -/
def v5ScalarODE (p : ℕ → Polynomial K) (N : ℕ) (x : PowerSeries K) : PowerSeries K :=
  ∑ i ∈ Finset.range N, (p i : PowerSeries K) * ((PowerSeries.derivative K)^[i] x)

/-- Exact grouped coefficient formula, valid for arbitrary input series. -/
theorem v5_scalar_grouped_coefficient (p : ℕ → Polynomial K) (N D : ℕ)
    (hdeg : ∀ i < N, (p i).natDegree ≤ D) (x : PowerSeries K) (n : ℕ) :
    ∑ j ∈ Finset.range (D+N), (stage26_odeSymbol p N D j).eval (n : K) *
      PowerSeries.coeff K (n+j) x = PowerSeries.coeff K (n+D) (v5ScalarODE p N x) := by
  simp only [stage26_odeSymbol, eval_finset_sum, eval_mul, eval_C, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [v5ScalarODE, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp_rw [mul_assoc]
  rw [stage26_odeSymbolScalar_sum p N D i (Finset.mem_range.mp hi)]
  rw [stage26_coeff_polynomial_mul _ _ D n (hdeg i (Finset.mem_range.mp hi))]
  apply Finset.sum_congr rfl
  intro k hk
  rw [stage26_coeff_iterate_derivative]
  have hkD : k ≤ D := by have := Finset.mem_range.mp hk; omega
  have heq : n+D-k+i = n+(D+i-k) := by omega
  simp only [stage26_shiftedFalling, eval_comp, eval_add, eval_X, eval_C,
    ← Nat.cast_add, heq]

/-- Truncation to the genuine highest shift loses no coefficient information. -/
theorem v5_scalar_leading_coefficient (p : ℕ → Polynomial K) (N D h : ℕ)
    (hdeg : ∀ i < N, (p i).natDegree ≤ D) (hh : h < D+N)
    (hz : ∀ j, h < j → stage26_odeSymbol p N D j = 0)
    (x : PowerSeries K) (n : ℕ) :
    ∑ j ∈ Finset.range (h+1), (stage26_odeSymbol p N D j).eval (n : K) *
      PowerSeries.coeff K (n+j) x = PowerSeries.coeff K (n+D) (v5ScalarODE p N x) := by
  rw [← v5_scalar_grouped_coefficient p N D hdeg x n]
  apply Finset.sum_subset (Finset.range_mono (by omega : h+1 ≤ D+N))
  intro j hj hjnot
  have hgreater : h < j := by
    have : ¬ j < h+1 := by simpa only [Finset.mem_range] using hjnot
    omega
  simp [hz j hgreater]

/-- An exact finite-early-equations / triangular-tail decomposition. -/
theorem v5_scalar_ode_iff_early_and_tail (p : ℕ → Polynomial K) (N D h c : ℕ)
    (hdeg : ∀ i < N, (p i).natDegree ≤ D) (hh : h < D+N)
    (hz : ∀ j, h < j → stage26_odeSymbol p N D j = 0)
    (x : PowerSeries K) :
    v5ScalarODE p N x = 0 ↔
      (∀ t < c+D, PowerSeries.coeff K t (v5ScalarODE p N x) = 0) ∧
      (∀ n ≥ c, ∑ j ∈ Finset.range (h+1),
        (stage26_odeSymbol p N D j).eval (n : K) * PowerSeries.coeff K (n+j) x = 0) := by
  simp_rw [v5_scalar_leading_coefficient p N D h hdeg hh hz]
  constructor
  · intro hx
    simp [hx]
  · rintro ⟨he,ht⟩
    ext t
    simp only [map_zero]
    by_cases hearly : t < c+D
    · exact he t hearly
    · have hlate := ht (t-D) (by omega)
      simpa only [Nat.sub_add_cancel (by omega : D ≤ t)] using hlate

/-- Vanishing higher symbols forces every offending monomial coefficient to vanish. -/
theorem v5_scalar_coefficient_shift_bound (p : ℕ → Polynomial K) (N D h i k : ℕ)
    (hdeg : ∀ i < N, (p i).natDegree ≤ D)
    (hz : ∀ j, h < j → stage26_odeSymbol p N D j = 0)
    (hi : i < N) (hk : (p i).coeff k ≠ 0) : D+i-k ≤ h := by
  have hkD : k ≤ D := (le_natDegree_of_ne_zero hk).trans (hdeg i hi)
  by_contra hn
  have hh := (stage26_odeSymbol_eq_zero_iff p N D (D+i-k)).mp (hz _ (by omega)) i hi
  have hguard : D+i-k ≤ D+i ∧ D+i-(D+i-k) ≤ D := by omega
  have heq : D+i-(D+i-k) = k := by omega
  unfold stage26_odeSymbolScalar at hh
  rw [if_pos hguard, heq] at hh
  exact hk hh

/-- The finitely many early ODE equations depend only on the first c+h inputs. -/
theorem v5_scalar_early_depends_on_jet (p : ℕ → Polynomial K) (N D h c : ℕ)
    (hdeg : ∀ i < N, (p i).natDegree ≤ D)
    (hz : ∀ j, h < j → stage26_odeSymbol p N D j = 0)
    (x y : PowerSeries K)
    (hxy : ∀ k < c+h, PowerSeries.coeff K k x = PowerSeries.coeff K k y)
    (t : ℕ) (ht : t < c+D) :
    PowerSeries.coeff K t (v5ScalarODE p N x) =
      PowerSeries.coeff K t (v5ScalarODE p N y) := by
  simp only [v5ScalarODE, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ab hab
  have hab' : ab.1 + ab.2 = t := Finset.mem_antidiagonal.mp hab
  simp only [Polynomial.coeff_coe, stage26_coeff_iterate_derivative]
  by_cases hk : (p i).coeff ab.1 = 0
  · simp [hk]
  · have hkD : ab.1 ≤ D :=
      (le_natDegree_of_ne_zero hk).trans (hdeg i (Finset.mem_range.mp hi))
    have hs := v5_scalar_coefficient_shift_bound p N D h i ab.1 hdeg hz
      (Finset.mem_range.mp hi) hk
    rw [hxy (ab.2+i) (by omega)]

/-- Symbols and their exact support commute with field embeddings. -/
theorem v5_scalar_symbol_map {L : Type*} [Field L] (φ : K →+* L)
    (p : ℕ → Polynomial K) (N D j : ℕ) :
    (stage26_odeSymbol p N D j).map φ =
      stage26_odeSymbol (fun i => (p i).map φ) N D j := by
  classical
  simp only [stage26_odeSymbol, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  · simp only [stage26_odeSymbolScalar, apply_ite φ, map_zero, coeff_map]
  · simp [stage26_shiftedFalling, Polynomial.map_comp, descPochhammer_map]

#print axioms v5_scalar_coefficient_shift_bound
#print axioms v5_scalar_early_depends_on_jet
#print axioms v5_scalar_symbol_map
#print axioms v5_polynomial_nat_eventually_ne
#print axioms v5_scalar_indicial_recurrence
#print axioms v5_scalar_grouped_coefficient
#print axioms v5_scalar_ode_iff_early_and_tail
end StrictEUnit
