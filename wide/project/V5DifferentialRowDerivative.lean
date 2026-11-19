import V5FactorRegularPoint

namespace StrictEUnit
open scoped Topology BigOperators
open Filter

noncomputable def v5FunctionRow (a : ℕ → ℂ → ℂ) (m : ℕ)
    (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (m+1), a k z * iteratedDeriv k f z

/-- Zero-extend the coefficient row before taking its derivative or shifting
it by one position. -/
noncomputable def v5TruncateRow (a : ℕ → ℂ → ℂ) (m k : ℕ) : ℂ → ℂ :=
  if k ≤ m then a k else 0

noncomputable def v5DifferentiateRow (a : ℕ → ℂ → ℂ) (m k : ℕ) (z : ℂ) : ℂ :=
  deriv (v5TruncateRow a m k) z +
    (match k with
    | 0 => 0
    | j+1 => v5TruncateRow a m j z)

private theorem v5_derivativeRow_iterated_analytic {f : ℂ → ℂ} {x : ℂ}
    (hf : AnalyticAt ℂ f x) (k : ℕ) : AnalyticAt ℂ (iteratedDeriv k f) x := by
  simpa only [iteratedDeriv_eq_iterate] using hf.iterated_deriv k

theorem v5_differentiateRow_analyticAt {a : ℕ → ℂ → ℂ} {x : ℂ} {m : ℕ}
    (ha : ∀ k, AnalyticAt ℂ (a k) x) (k : ℕ) :
    AnalyticAt ℂ (v5DifferentiateRow a m k) x := by
  have ht (j : ℕ) : AnalyticAt ℂ (v5TruncateRow a m j) x := by
    unfold v5TruncateRow
    split
    · exact ha j
    · exact analyticAt_const
  cases k with
  | zero =>
    change AnalyticAt ℂ (fun z => deriv (v5TruncateRow a m 0) z + (0 : ℂ)) x
    exact (ht 0).deriv.add analyticAt_const
  | succ k => exact (ht (k+1)).deriv.add (ht k)

/-- Differentiating the action is the action of the differentiated
coefficient row. This is the single-step product rule for differential rows. -/
theorem v5_deriv_functionRow {a : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {x : ℂ}
    (ha : ∀ k, AnalyticAt ℂ (a k) x) (hf : AnalyticAt ℂ f x) (m : ℕ) :
    deriv (v5FunctionRow a m f) x =
      v5FunctionRow (v5DifferentiateRow a m) (m+1) f x := by
  have hder := (HasDerivAt.sum (u := Finset.range (m+1)) fun k _ =>
    (ha k).differentiableAt.hasDerivAt.mul
      (v5_derivativeRow_iterated_analytic hf k).differentiableAt.hasDerivAt).deriv
  unfold v5FunctionRow
  rw [hder]
  simp only [← iteratedDeriv_succ, Finset.sum_add_distrib, v5DifferentiateRow, add_mul]
  congr 1
  · rw [Finset.sum_range_succ (f := fun k => deriv (v5TruncateRow a m k) x *
        iteratedDeriv k f x)]
    have ht : v5TruncateRow a m (m+1) = 0 := by simp [v5TruncateRow]
    rw [ht]
    simp only [Pi.zero_apply, show deriv (0 : ℂ → ℂ) x = 0 from deriv_const x 0,
      zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    have hkm : k ≤ m := by have := Finset.mem_range.mp hk; omega
    simp [v5TruncateRow, hkm]
  · rw [Finset.sum_range_succ' (f := fun k => (match k with
        | 0 => 0
        | j+1 => v5TruncateRow a m j x) * iteratedDeriv k f x)]
    simp only [zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    have hkm : k ≤ m := by have := Finset.mem_range.mp hk; omega
    simp [v5TruncateRow, hkm, mul_comm]

noncomputable def v5IterateRow (a : ℕ → ℂ → ℂ) (m : ℕ) : ℕ → ℕ → ℂ → ℂ
  | 0 => a
  | j+1 => v5DifferentiateRow (v5IterateRow a m j) (m+j)

theorem v5_iterateRow_analyticAt {a : ℕ → ℂ → ℂ} {x : ℂ}
    (ha : ∀ k, AnalyticAt ℂ (a k) x) (m j k : ℕ) :
    AnalyticAt ℂ (v5IterateRow a m j k) x := by
  induction j generalizing k with
  | zero => exact ha k
  | succ j ih => exact v5_differentiateRow_analyticAt ih k

theorem v5_iteratedDeriv_functionRow {a : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {S : Set ℂ}
    (ho : IsOpen S) (ha : ∀ k, AnalyticOnNhd ℂ (a k) S) (hf : AnalyticOnNhd ℂ f S)
    (m j : ℕ) (x : ℂ) (hx : x ∈ S) :
    iteratedDeriv j (v5FunctionRow a m f) x = v5FunctionRow (v5IterateRow a m j) (m+j) f x := by
  induction j generalizing x with
  | zero => simp [iteratedDeriv_zero, v5IterateRow]
  | succ j ih =>
    have he : iteratedDeriv j (v5FunctionRow a m f) =ᶠ[𝓝 x]
        v5FunctionRow (v5IterateRow a m j) (m+j) f := by
      filter_upwards [ho.mem_nhds hx] with z hz
      exact ih z hz
    rw [iteratedDeriv_succ, he.deriv.eq_of_nhds]
    exact v5_deriv_functionRow
      (fun k => v5_iterateRow_analyticAt (fun l => ha l x hx) m j k) (hf x hx) (m+j)

#print axioms v5_differentiateRow_analyticAt
#print axioms v5_deriv_functionRow
#print axioms v5_iteratedDeriv_functionRow
end StrictEUnit
