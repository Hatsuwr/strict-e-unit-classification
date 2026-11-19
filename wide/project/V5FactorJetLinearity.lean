import V5FactorJetKernel

namespace StrictEUnit
open scoped Topology BigOperators
open Filter

private theorem v5_iteratedDeriv_zero_fun (n : ℕ) :
    iteratedDeriv n (fun _ : ℂ => (0 : ℂ)) = fun _ => 0 := by
  induction n with
  | zero => rw [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    exact deriv_const z 0

private theorem v5_iteratedDeriv_finite_weighted_sum {ι : Type*}
    {u : ι → ℂ → ℂ} {z : ℂ} (n : ℕ) (c : ι → ℂ) (s : Finset ι)
    (hu : ∀ i, AnalyticAt ℂ (u i) z) :
    iteratedDeriv n (fun w => ∑ i ∈ s, c i * u i w) z =
      ∑ i ∈ s, c i * iteratedDeriv n (u i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [v5_iteratedDeriv_zero_fun]
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    have hfirst : ContDiffAt ℂ n (fun w => c i * u i w) z :=
      contDiffAt_const.mul (hu i).contDiffAt
    have hrest : ContDiffAt ℂ n (fun w => ∑ j ∈ s, c j * u j w) z :=
      ContDiffAt.sum fun j _ => contDiffAt_const.mul (hu j).contDiffAt
    change iteratedDeriv n ((fun w => c i * u i w) +
      (fun w => ∑ j ∈ s, c j * u j w)) z = _
    rw [iteratedDeriv_add hfirst hrest, iteratedDeriv_const_mul (hu i).contDiffAt, ih]

/-- An initial-jet constraint measures exactly the corresponding derivative of
the weighted image, not merely a formal linear combination of coefficients. -/
theorem v5_initialJetMap_apply_eq_iteratedDeriv {n s : ℕ} {y : ℂ}
    {image : Fin n → ℂ → ℂ} (ha : ∀ j, AnalyticAt ℂ (image j) y)
    (c : Fin n → ℂ) (i : Fin s) :
    v5FactorInitialJetMap s image y c i =
      iteratedDeriv i.val (v5WeightedGerm image c) y := by
  change (∑ j, c j * iteratedDeriv i.val (image j) y) =
    iteratedDeriv i.val (fun w => ∑ j, c j * image j w) y
  exact (v5_iteratedDeriv_finite_weighted_sum i.val c Finset.univ ha).symm

theorem v5_initialJetMap_eq_zero_iff {n s : ℕ} {y : ℂ}
    {image : Fin n → ℂ → ℂ} (ha : ∀ j, AnalyticAt ℂ (image j) y)
    (c : Fin n → ℂ) :
    v5FactorInitialJetMap s image y c = 0 ↔
      ∀ k < s, iteratedDeriv k (v5WeightedGerm image c) y = 0 := by
  constructor
  · intro h k hk
    have e := congrFun h ⟨k, hk⟩
    rw [v5_initialJetMap_apply_eq_iteratedDeriv ha] at e
    exact e
  · intro h
    funext i
    rw [v5_initialJetMap_apply_eq_iteratedDeriv ha]
    exact h i.val i.isLt

/-- The polynomial differential residual commutes with finite constant
linear combinations at a point where the summands are analytic. -/
theorem v5_rowResidual_weightedGerm {K : Type*} [Field K] [Algebra K ℂ]
    {n : ℕ} {z : ℂ} {u : Fin n → ℂ → ℂ}
    (ha : ∀ j, AnalyticAt ℂ (u j) z) (c : Fin n → ℂ)
    (m : ℕ) (q : ℕ → Polynomial K) :
    v5RowResidual (v5WeightedGerm u c) m q z =
      v5WeightedGerm (fun j w => v5RowResidual (u j) m q w) c z := by
  classical
  unfold v5RowResidual v5WeightedGerm
  simp only [v5_iteratedDeriv_finite_weighted_sum _ c Finset.univ ha, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem v5_iteratedDeriv_analyticAt {f : ℂ → ℂ} {z : ℂ}
    (h : AnalyticAt ℂ f z) (k : ℕ) : AnalyticAt ℂ (iteratedDeriv k f) z := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using h
  | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv

private theorem v5_finite_sum_analyticAt {ι : Type*} {f : ι → ℂ → ℂ}
    {z : ℂ} (s : Finset ι) (h : ∀ i, AnalyticAt ℂ (f i) z) :
    AnalyticAt ℂ (fun w => ∑ i ∈ s, f i w) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) z)
  | insert i s hi ih => simpa only [Finset.sum_insert hi] using (h i).add ih

theorem v5_rowResidual_analyticAt {K : Type*} [Field K] [Algebra K ℂ]
    {f : ℂ → ℂ} {z : ℂ} (h : AnalyticAt ℂ f z)
    (m : ℕ) (q : ℕ → Polynomial K) :
    AnalyticAt ℂ (v5RowResidual f m q) z := by
  apply v5_finite_sum_analyticAt
  intro j
  apply AnalyticAt.mul _ (v5_iteratedDeriv_analyticAt h j)
  change AnalyticAt ℂ (fun w => (q j).eval₂ (algebraMap K ℂ) w) z
  simp_rw [Polynomial.eval₂_eq_eval_map (algebraMap K ℂ)]
  simpa only [Polynomial.aeval_def] using
    (analyticAt_id : AnalyticAt ℂ (fun w : ℂ => w) z).aeval_polynomial
      ((q j).map (algebraMap K ℂ))

/-- Vanishing near a nearby regular point propagates across any preconnected
analyticity neighborhood of the mark; the quotient need not be ordinary there. -/
theorem v5_rowResidual_eventually_zero_at_mark {K : Type*} [Field K] [Algebra K ℂ]
    {f : ℂ → ℂ} {x y : ℂ} {D : Set ℂ} (hD : IsPreconnected D)
    (hx : D ∈ 𝓝 x) (hy : y ∈ D)
    (hf : AnalyticOnNhd ℂ f D) (m : ℕ) (q : ℕ → Polynomial K)
    (hzero : ∀ᶠ z in 𝓝 y, v5RowResidual f m q z = 0) :
    ∀ᶠ z in 𝓝 x, v5RowResidual f m q z = 0 := by
  have ha : AnalyticOnNhd ℂ (v5RowResidual f m q) D :=
    fun z hz => v5_rowResidual_analyticAt (hf z hz) m q
  have hz : v5RowResidual f m q =ᶠ[𝓝 y] 0 := hzero
  exact (Filter.eventually_of_mem hx)
    (ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero hD hy hz)

#print axioms v5_initialJetMap_apply_eq_iteratedDeriv
#print axioms v5_initialJetMap_eq_zero_iff
#print axioms v5_rowResidual_weightedGerm
#print axioms v5_rowResidual_analyticAt
#print axioms v5_rowResidual_eventually_zero_at_mark
end StrictEUnit
