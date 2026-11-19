import V5DifferentialRowDerivative

namespace StrictEUnit
open scoped Topology BigOperators

/-- Coefficient collection in the product with the left operator acting last. -/
noncomputable def v5ComposeRows (b a : ℕ → ℂ → ℂ) (r m k : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (r+1), b j z * v5TruncateRow (v5IterateRow a m j) (m+j) k z

theorem v5_truncateRow_padding (a : ℕ → ℂ → ℂ) {m t : ℕ} (h : m ≤ t)
    (f : ℂ → ℂ) (z : ℂ) :
    v5FunctionRow (v5TruncateRow a m) t f z = v5FunctionRow a m f z := by
  unfold v5FunctionRow
  symm
  calc
    (∑ k ∈ Finset.range (m+1), a k z * iteratedDeriv k f z) =
        ∑ k ∈ Finset.range (m+1), v5TruncateRow a m k z * iteratedDeriv k f z := by
          apply Finset.sum_congr rfl
          intro k hk
          have hkm := Finset.mem_range.mp hk
          simp [v5TruncateRow, show k ≤ m by omega]
    _ = ∑ k ∈ Finset.range (t+1), v5TruncateRow a m k z * iteratedDeriv k f z := by
          apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ h))
          intro k _ hk
          have hkm : ¬ k ≤ m := by
            intro hk'
            exact hk (Finset.mem_range.mpr (by omega))
          simp [v5TruncateRow, hkm]

/-- On an open analytic domain, applying two rows in succession agrees
pointwise with applying the collected product row of cutoff m+r. -/
theorem v5_functionRow_compose {a : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {S : Set ℂ}
    (ho : IsOpen S) (ha : ∀ k, AnalyticOnNhd ℂ (a k) S) (hf : AnalyticOnNhd ℂ f S)
    (b : ℕ → ℂ → ℂ) (r m : ℕ) (z : ℂ) (hz : z ∈ S) :
    v5FunctionRow b r (v5FunctionRow a m f) z =
      v5FunctionRow (v5ComposeRows b a r m) (m+r) f z := by
  unfold v5FunctionRow at *
  change (∑ j ∈ Finset.range (r+1), b j z * iteratedDeriv j (v5FunctionRow a m f) z) =
    ∑ k ∈ Finset.range (m+r+1), v5ComposeRows b a r m k z * iteratedDeriv k f z
  calc
    _ = ∑ j ∈ Finset.range (r+1), b j z *
        v5FunctionRow (v5TruncateRow (v5IterateRow a m j) (m+j)) (m+r) f z := by
      apply Finset.sum_congr rfl
      intro j hj
      have h := Finset.mem_range.mp hj
      rw [v5_truncateRow_padding _ (show m+j ≤ m+r by omega),
        v5_iteratedDeriv_functionRow ho ha hf m j z hz]
    _ = _ := by
      unfold v5FunctionRow v5ComposeRows
      simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]

/-- A cleared polynomial row is the special case of its pointwise
coefficient functions, before any denominator is introduced. -/
theorem v5_rowResidual_eq_functionRow {K : Type*} [Field K] [Algebra K ℂ]
    (p : ℕ → Polynomial K) (m : ℕ) (f : ℂ → ℂ) :
    v5RowResidual f m p =
      v5FunctionRow (fun k z => (p k).eval₂ (algebraMap K ℂ) z) m f := rfl

theorem v5_iterateRow_top (a : ℕ → ℂ → ℂ) (m j : ℕ) (z : ℂ) :
    v5IterateRow a m j (m+j) z = a m z := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change deriv (v5TruncateRow (v5IterateRow a m j) (m+j) (m+j+1)) z +
      v5TruncateRow (v5IterateRow a m j) (m+j) (m+j) z = _
    simp [v5TruncateRow, show ¬ m+j+1 ≤ m+j by omega,
      show deriv (0 : ℂ → ℂ) z = 0 from deriv_const z 0, ih]

/-- In the highest position only the top left coefficient contributes,
so the top coefficient is the commutative product of the two top coefficients. -/
theorem v5_composeRows_top (b a : ℕ → ℂ → ℂ) (r m : ℕ) (z : ℂ) :
    v5ComposeRows b a r m (m+r) z = b r z * a m z := by
  unfold v5ComposeRows
  rw [Finset.sum_range_succ]
  have hzero : (∑ j ∈ Finset.range r, b j z *
      v5TruncateRow (v5IterateRow a m j) (m+j) (m+r) z) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have h := Finset.mem_range.mp hj
    simp [v5TruncateRow, show ¬ m+r ≤ m+j by omega]
  rw [hzero, zero_add]
  simp [v5TruncateRow, v5_iterateRow_top]

#print axioms v5_truncateRow_padding
#print axioms v5_functionRow_compose
#print axioms v5_rowResidual_eq_functionRow
#print axioms v5_iterateRow_top
#print axioms v5_composeRows_top
end StrictEUnit
