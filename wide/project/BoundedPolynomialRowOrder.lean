import FormalSeriesFiniteJets
import Mathlib.Algebra.Polynomial.Degree.Support

/-!
NEW SOURCE-ONLY: bounded polynomial rows act inside the finite-dimensional
span of the SAME finitely many shifted series. A uniform order bound follows
for every NONZERO action. The original family need not be independent. This
does not provide the separate uniform degree bound for system annihilators.
-/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

variable {K I : Type*} [Field K] [Fintype I]

/-- Exact bounded-degree polynomial expansion inside ordinary power series. -/
theorem powerSeries_polynomial_expansion_of_natDegree_le
    (p : Polynomial K) (d : ℕ) (hd : p.natDegree ≤ d) :
    (p : PowerSeries K) = ∑ j ∈ Finset.range (d + 1),
      p.coeff j • (PowerSeries.X ^ j : PowerSeries K) := by
  have hp : p = ∑ j ∈ Finset.range (d + 1),
      Polynomial.C (p.coeff j) * Polynomial.X ^ j := by
    simpa only [Polynomial.C_mul_X_pow_eq_monomial] using
      p.as_sum_range' (d + 1) (Nat.lt_succ_of_le hd)
  have hmap := congrArg (Polynomial.coeToPowerSeries.ringHom (R := K)) hp
  simpa only [map_sum, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow,
    Polynomial.coe_X, PowerSeries.smul_eq_C_mul] using hmap

/-- Each literal polynomial row action of degree at most d belongs to the span
of X^j*f_i for i in the original finite family and 0 <= j <= d. -/
theorem powerSeries_polynomial_row_mem_shift_span
    (f : I → PowerSeries K) (d : ℕ) (P : I → Polynomial K)
    (hdeg : ∀ i, (P i).natDegree ≤ d) :
    (∑ i, (P i : PowerSeries K) * f i) ∈ Submodule.span K
      (Set.range (fun ij : I × Fin (d + 1) =>
        (PowerSeries.X ^ ij.2.val : PowerSeries K) * f ij.1)) := by
  classical
  let S : Submodule K (PowerSeries K) := Submodule.span K
    (Set.range (fun ij : I × Fin (d + 1) =>
      (PowerSeries.X ^ ij.2.val : PowerSeries K) * f ij.1))
  apply Submodule.sum_mem S
  intro i hi
  rw [powerSeries_polynomial_expansion_of_natDegree_le (P i) d (hdeg i),
    Finset.sum_mul]
  apply Submodule.sum_mem S
  intro j hj
  rw [smul_mul_assoc]
  exact S.smul_mem ((P i).coeff j)
    (Submodule.subset_span ⟨(i, ⟨j, Finset.mem_range.mp hj⟩), rfl⟩)

/-- One bound, depending only on the SAME finite family and d, detects every
nonzero row action of that degree. This includes dependent or zero families;
the nonzero-action premise is then essential and is not silently discarded. -/
theorem powerSeries_bounded_polynomial_row_order
    (f : I → PowerSeries K) (d : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ P : I → Polynomial K,
      (∀ i, (P i).natDegree ≤ d) →
      (∑ i, (P i : PowerSeries K) * f i) ≠ 0 →
      ∃ n < N, PowerSeries.coeff K n (∑ i, (P i : PowerSeries K) * f i) ≠ 0 ∧
        (∑ i, (P i : PowerSeries K) * f i).order ≤ (n : ℕ∞) := by
  classical
  let S : Submodule K (PowerSeries K) := Submodule.span K
    (Set.range (fun ij : I × Fin (d + 1) =>
      (PowerSeries.X ^ ij.2.val : PowerSeries K) * f ij.1))
  letI : FiniteDimensional K S :=
    FiniteDimensional.span_of_finite K (Set.finite_range _)
  obtain ⟨N, hN, hbound⟩ := powerSeries_subspace_order_bound S
  refine ⟨N, hN, fun P hdeg hne => ?_⟩
  exact hbound _ (powerSeries_polynomial_row_mem_shift_span f d P hdeg) hne

end StrictEUnit
end
