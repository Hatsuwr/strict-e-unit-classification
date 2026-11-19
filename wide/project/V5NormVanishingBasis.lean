import V5MinimalRowLocalEquivalence

namespace StrictEUnit
open scoped Topology BigOperators
open Filter

private theorem v5_affine_polynomial_ne_zero (K : Type*) [Field K] :
    (1 - Polynomial.X : Polynomial K) ≠ 0 := by
  intro h
  have hc := congrArg (fun p : Polynomial K => p.coeff 1) h
  simp [Polynomial.coeff_one] at hc

private theorem v5_affine_polynomial_eval {K : Type*} [Field K] [Algebra K ℂ] (z : ℂ) :
    (Polynomial.eval₂RingHom (algebraMap K ℂ) z) (1 - Polynomial.X) = 1 - z := by
  simp

private theorem v5_reverse_affine_residual {K : Type*} [Field K] [Algebra K ℂ]
    {u : ℂ → ℂ} {z : ℂ} (hu : AnalyticAt ℂ u z)
    (m : ℕ) (q : ℕ → Polynomial K) :
    v5RowResidual (fun z => (1 - z) * u z) m
      (v5ReverseAnnihilator (1 - Polynomial.X) m q) z =
        (1 - z) ^ (m + 1) * v5RowResidual u m q z := by
  unfold v5RowResidual
  rw [← v5_affine_polynomial_eval (K := K) z]
  exact
    (v5_reverseAnnihilator_eval (Polynomial.eval₂RingHom (algebraMap K ℂ) z)
      (1 - Polynomial.X) (fun j => iteratedDeriv j (fun w => (1 - w) * u w) z)
      (fun j => iteratedDeriv j u z)
      (by simp [iteratedDeriv_zero, v5_affine_polynomial_eval])
      (by intro j; rw [v5_affine_polynomial_eval]; exact v5_affine_iteratedDeriv_succ hu j)
      m q)

private theorem v5_analyticAt_affine_product {u : ℂ → ℂ} {x : ℂ}
    (hu : AnalyticAt ℂ u x) : AnalyticAt ℂ (fun z => (1 - z) * u z) x :=
  (((analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) x).sub analyticAt_id).mul hu)

theorem v5_norm_row_of_quotient_local_solution {K : Type*} [Field K] [Algebra K ℂ]
    {g u : ℂ → ℂ} {x : ℂ} (hg : ∀ z, AnalyticAt ℂ g z)
    (hu : AnalyticAt ℂ u x) (m : ℕ) (a q : ℕ → Polynomial K)
    (ha : a m ≠ 0) (hq : q m ≠ 0)
    (hmin : ∀ n < m, ¬ v5HasAnnihilatorOrder K (fun z => (1 - z) * g z) n)
    (haSol : ∀ z, v5RowResidual (fun w => (1 - w) * g w) m a z = 0)
    (hqSol : ∀ z, v5RowResidual g m q z = 0)
    (huSol : ∀ᶠ z in 𝓝 x, v5RowResidual u m q z = 0) :
    ∀ᶠ z in 𝓝 x, v5RowResidual (fun w => (1 - w) * u w) m a z = 0 := by
  let b : ℕ → Polynomial K := v5ReverseAnnihilator (1 - Polynomial.X) m q
  have hb : b m ≠ 0 :=
    v5_reverseAnnihilator_top_ne_zero _ m q (v5_affine_polynomial_ne_zero K) hq
  have hbSol (z : ℂ) : v5RowResidual (fun w => (1 - w) * g w) m b z = 0 := by
    dsimp only [b]
    rw [v5_reverse_affine_residual (hg z), hqSol z, mul_zero]
  apply (v5_minimal_rows_local_zero_iff hmin b a hb ha hbSol haSol
    (v5_analyticAt_affine_product hu)).mp
  filter_upwards [hu.eventually_analyticAt, huSol] with z hz hzero
  dsimp only [b]
  rw [v5_reverse_affine_residual hz, hzero, mul_zero]

/-- Independence of a finite family as germs; no span or dimension claim is built in. -/
def v5FiniteGermIndependent {ι : Type*} [Fintype ι] (x : ℂ) (u : ι → ℂ → ℂ) : Prop :=
  ∀ c : ι → ℂ, (∀ᶠ z in 𝓝 x, (∑ i, c i * u i z) = 0) → ∀ i, c i = 0

private theorem v5_cancel_affine_eventually {r : ℂ → ℂ} {x : ℂ}
    (hr : ∀ᶠ z in 𝓝 x, ContinuousAt r z)
    (hz : ∀ᶠ z in 𝓝 x, (1 - z) * r z = 0) :
    ∀ᶠ z in 𝓝 x, r z = 0 := by
  have hd : Dense {z : ℂ | 1 - z ≠ 0} := by
    simpa only [v5_affine_polynomial_eval] using
      (v5_dense_polynomial_eval_ne_zero (1 - Polynomial.X : Polynomial ℂ)
        (v5_affine_polynomial_ne_zero ℂ))
  filter_upwards [hz.eventually_nhds, hr] with y hy hc
  refine tendsto_nhds_unique_of_frequently_eq hc tendsto_const_nhds ?_
  exact ((mem_closure_iff_frequently.mp (hd y)).and_eventually hy).mono
    fun z ⟨hnz, hzero⟩ => (mul_eq_zero.mp hzero).resolve_left hnz

theorem v5_affine_preserves_finite_germ_independence {ι : Type*} [Fintype ι]
    {u : ι → ℂ → ℂ} {x : ℂ} (hu : ∀ i, AnalyticAt ℂ (u i) x)
    (hind : v5FiniteGermIndependent x u) :
    v5FiniteGermIndependent x (fun i z => (1 - z) * u i z) := by
  classical
  intro c hc
  apply hind c
  apply v5_cancel_affine_eventually
  · have hAll : ∀ᶠ z in 𝓝 x, ∀ i, AnalyticAt ℂ (u i) z :=
      Filter.eventually_all.mpr fun i => (hu i).eventually_analyticAt
    filter_upwards [hAll] with z hz
    apply tendsto_finset_sum
    intro i _
    exact continuousAt_const.mul (hz i).continuousAt
  · filter_upwards [hc] with z hz
    rw [Finset.mul_sum]
    convert hz using 1
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Given an independent family of holomorphic quotient solutions, the transported
family is independent, vanishes at 1, and solves the chosen minimum-order norm row. -/
theorem v5_norm_vanishing_family_of_quotient {K ι : Type*}
    [Field K] [Algebra K ℂ] [Fintype ι] {g : ℂ → ℂ} {u : ι → ℂ → ℂ}
    (hg : ∀ z, AnalyticAt ℂ g z) (hu : ∀ i, AnalyticAt ℂ (u i) 1)
    (m : ℕ) (a q : ℕ → Polynomial K) (ha : a m ≠ 0) (hq : q m ≠ 0)
    (hmin : ∀ n < m, ¬ v5HasAnnihilatorOrder K (fun z => (1 - z) * g z) n)
    (haSol : ∀ z, v5RowResidual (fun w => (1 - w) * g w) m a z = 0)
    (hqSol : ∀ z, v5RowResidual g m q z = 0)
    (huSol : ∀ i, ∀ᶠ z in 𝓝 (1 : ℂ), v5RowResidual (u i) m q z = 0)
    (hind : v5FiniteGermIndependent 1 u) :
    ∃ v : ι → ℂ → ℂ, v5FiniteGermIndependent 1 v ∧
      ∀ i, AnalyticAt ℂ (v i) 1 ∧ v i 1 = 0 ∧
        ∀ᶠ z in 𝓝 (1 : ℂ), v5RowResidual (v i) m a z = 0 := by
  refine ⟨fun i z => (1 - z) * u i z, v5_affine_preserves_finite_germ_independence hu hind, ?_⟩
  intro i
  exact ⟨v5_analyticAt_affine_product (hu i), by simp,
    v5_norm_row_of_quotient_local_solution hg (hu i) m a q ha hq hmin haSol hqSol (huSol i)⟩

#print axioms v5_norm_row_of_quotient_local_solution
#print axioms v5_affine_preserves_finite_germ_independence
#print axioms v5_norm_vanishing_family_of_quotient
end StrictEUnit
