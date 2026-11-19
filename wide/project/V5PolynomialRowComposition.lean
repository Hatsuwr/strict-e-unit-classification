import V5DifferentialRowComposition

namespace StrictEUnit
open scoped Topology BigOperators

variable {K : Type*} [Field K] [Algebra K ℂ]

noncomputable def v5EvalPolynomialRow (a : ℕ → Polynomial K) : ℕ → ℂ → ℂ :=
  fun k z => (a k).eval₂ (algebraMap K ℂ) z

noncomputable def v5TruncatePolynomialRow (a : ℕ → Polynomial K) (m k : ℕ) : Polynomial K :=
  if k ≤ m then a k else 0

noncomputable def v5DifferentiatePolynomialRow (a : ℕ → Polynomial K) (m k : ℕ) : Polynomial K :=
  (v5TruncatePolynomialRow a m k).derivative +
    (match k with | 0 => 0 | j+1 => v5TruncatePolynomialRow a m j)

noncomputable def v5IteratePolynomialRow (a : ℕ → Polynomial K) (m : ℕ) : ℕ → ℕ → Polynomial K
  | 0 => a
  | j+1 => v5DifferentiatePolynomialRow (v5IteratePolynomialRow a m j) (m+j)

noncomputable def v5ComposePolynomialRows (b a : ℕ → Polynomial K) (r m k : ℕ) : Polynomial K :=
  ∑ j ∈ Finset.range (r+1), b j * v5TruncatePolynomialRow (v5IteratePolynomialRow a m j) (m+j) k

theorem v5_evalPolynomialRow_truncate (a : ℕ → Polynomial K) (m : ℕ) :
    v5EvalPolynomialRow (v5TruncatePolynomialRow a m) =
      v5TruncateRow (v5EvalPolynomialRow a) m := by
  funext k z
  by_cases h : k ≤ m <;> simp [v5EvalPolynomialRow, v5TruncatePolynomialRow, v5TruncateRow, h]

theorem v5_evalPolynomialRow_differentiate (a : ℕ → Polynomial K) (m : ℕ) :
    v5EvalPolynomialRow (v5DifferentiatePolynomialRow a m) =
      v5DifferentiateRow (v5EvalPolynomialRow a) m := by
  funext k z
  have hd (q : Polynomial K) :
      deriv (fun w => q.eval₂ (algebraMap K ℂ) w) z =
        q.derivative.eval₂ (algebraMap K ℂ) z := by
    simpa only [Polynomial.aeval_def] using q.deriv_aeval (x := z)
  have hd' (k : ℕ) : deriv (v5EvalPolynomialRow (v5TruncatePolynomialRow a m) k) z =
      (v5TruncatePolynomialRow a m k).derivative.eval₂ (algebraMap K ℂ) z := hd _
  have ht := v5_evalPolynomialRow_truncate a m
  cases k with
  | zero =>
    change ((v5TruncatePolynomialRow a m 0).derivative + 0).eval₂ (algebraMap K ℂ) z =
      deriv (v5TruncateRow (v5EvalPolynomialRow a) m 0) z + 0
    rw [← ht]
    rw [hd']; simp only [add_zero]
  | succ k =>
    change ((v5TruncatePolynomialRow a m (k+1)).derivative +
      v5TruncatePolynomialRow a m k).eval₂ (algebraMap K ℂ) z =
      deriv (v5TruncateRow (v5EvalPolynomialRow a) m (k+1)) z +
      v5TruncateRow (v5EvalPolynomialRow a) m k z
    rw [← ht]
    rw [hd', Polynomial.eval₂_add]
    rfl

theorem v5_evalPolynomialRow_iterate (a : ℕ → Polynomial K) (m j : ℕ) :
    v5EvalPolynomialRow (v5IteratePolynomialRow a m j) =
      v5IterateRow (v5EvalPolynomialRow a) m j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [v5IteratePolynomialRow, v5IterateRow, v5_evalPolynomialRow_differentiate, ih]

theorem v5_evalPolynomialRow_compose (b a : ℕ → Polynomial K) (r m : ℕ) :
    v5EvalPolynomialRow (v5ComposePolynomialRows b a r m) =
      v5ComposeRows (v5EvalPolynomialRow b) (v5EvalPolynomialRow a) r m := by
  funext k z
  change (∑ j ∈ Finset.range (r+1), b j *
      v5TruncatePolynomialRow (v5IteratePolynomialRow a m j) (m+j) k).eval₂
      (algebraMap K ℂ) z = _
  rw [Polynomial.eval₂_finset_sum]
  unfold v5ComposeRows
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.eval₂_mul]
  change v5EvalPolynomialRow b j z *
      v5EvalPolynomialRow (v5TruncatePolynomialRow (v5IteratePolynomialRow a m j) (m+j)) k z = _
  rw [v5_evalPolynomialRow_truncate, v5_evalPolynomialRow_iterate]

omit [Algebra K ℂ] in
theorem v5_iteratePolynomialRow_top (a : ℕ → Polynomial K) (m j : ℕ) :
    v5IteratePolynomialRow a m j (m+j) = a m := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change (v5TruncatePolynomialRow (v5IteratePolynomialRow a m j) (m+j) (m+j+1)).derivative +
      v5TruncatePolynomialRow (v5IteratePolynomialRow a m j) (m+j) (m+j) = _
    simp [v5TruncatePolynomialRow, show ¬ m+j+1 ≤ m+j by omega, ih]

omit [Algebra K ℂ] in
theorem v5_composePolynomialRows_top (b a : ℕ → Polynomial K) (r m : ℕ) :
    v5ComposePolynomialRows b a r m (m+r) = b r * a m := by
  unfold v5ComposePolynomialRows
  rw [Finset.sum_range_succ]
  have hz : (∑ j ∈ Finset.range r, b j *
      v5TruncatePolynomialRow (v5IteratePolynomialRow a m j) (m+j) (m+r)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have := Finset.mem_range.mp hj
    simp [v5TruncatePolynomialRow, show ¬ m+r ≤ m+j by omega]
  rw [hz, zero_add]
  simp [v5TruncatePolynomialRow, v5_iteratePolynomialRow_top]

omit [Algebra K ℂ] in
theorem v5_composePolynomialRows_above (b a : ℕ → Polynomial K) (r m k : ℕ)
    (hk : m+r < k) : v5ComposePolynomialRows b a r m k = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  have := Finset.mem_range.mp hj
  simp [v5TruncatePolynomialRow, show ¬ k ≤ m+j by omega]

/-- Polynomial composition agrees with consecutive scalar row actions. -/
theorem v5_polynomialRows_compose_action (b a : ℕ → Polynomial K) (r m : ℕ)
    {S : Set ℂ} (ho : IsOpen S) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f S)
    {z : ℂ} (hz : z ∈ S) :
    v5RowResidual (v5RowResidual f m a) r b z =
      v5RowResidual f (m+r) (v5ComposePolynomialRows b a r m) z := by
  have ha : ∀ k, AnalyticOnNhd ℂ (v5EvalPolynomialRow a k) S := by
    intro k w _
    simpa only [v5EvalPolynomialRow, Polynomial.aeval_def] using
      (analyticAt_id : AnalyticAt ℂ (fun z : ℂ => z) w).aeval_polynomial (a k)
  have h := v5_functionRow_compose ho ha hf (v5EvalPolynomialRow b) r m z hz
  rw [← v5_evalPolynomialRow_compose] at h
  exact h

#print axioms v5_polynomialRows_compose_action
#print axioms v5_evalPolynomialRow_differentiate
#print axioms v5_evalPolynomialRow_iterate
#print axioms v5_evalPolynomialRow_compose
#print axioms v5_iteratePolynomialRow_top
#print axioms v5_composePolynomialRows_top
#print axioms v5_composePolynomialRows_above
end StrictEUnit
