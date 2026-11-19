import V5FactorJetLinearity

namespace StrictEUnit
open scoped Topology BigOperators
open Filter

private theorem v5_analytic_zero_of_all_jets {f : ℂ → ℂ} {x : ℂ}
    (hf : AnalyticAt ℂ f x) (h : ∀ n, iteratedDeriv n f x = 0) :
    f =ᶠ[𝓝 x] 0 := by
  have hp := hf.hasFPowerSeriesAt
  simp only [h, zero_div] at hp
  have hz : FormalMultilinearSeries.ofScalars ℂ (fun _ => 0) =
      (0 : FormalMultilinearSeries ℂ ℂ ℂ) := by
    ext n v
    simp [FormalMultilinearSeries.apply_eq_prod_smul_coeff]
  rw [hz] at hp
  exact hp.eventually_eq_zero

theorem v5_first_order_zero_of_zero_initial {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → ι → ℂ → ℂ} {U : ι → ℂ → ℂ} {x : ℂ}
    (hA : ∀ j k, AnalyticAt ℂ (A j k) x) (hu : ∀ j, AnalyticAt ℂ (U j) x)
    (hSys : ∀ j, ∀ᶠ z in 𝓝 x, deriv (U j) z = ∑ k, A j k z * U k z)
    (h0 : ∀ j, U j x = 0) (j : ι) : U j =ᶠ[𝓝 x] 0 := by
  apply v5_analytic_zero_of_all_jets (hu j)
  intro n
  simpa only [h0, mul_zero, Finset.sum_const_zero] using
    (v5_observableRow_iteratedDeriv hA hu hSys j n).eq_of_nhds

private theorem v5_jet_analyticAt {f : ℂ → ℂ} {x : ℂ}
    (hf : AnalyticAt ℂ f x) (n : ℕ) : AnalyticAt ℂ (iteratedDeriv n f) x := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv

/-- A scalar analytic solution at an ordinary point is determined by its initial jets.
The normalized equation is expressed as a finite sum of lower derivatives. -/
theorem v5_normalized_scalar_zero_of_zero_jets {s : ℕ} {f : ℂ → ℂ} {x : ℂ}
    (a : Fin s → ℂ → ℂ) (ha : ∀ j, AnalyticAt ℂ (a j) x)
    (hf : AnalyticAt ℂ f x)
    (he : ∀ᶠ z in 𝓝 x, iteratedDeriv s f z = ∑ j, a j z * iteratedDeriv j.val f z)
    (h0 : ∀ k < s, iteratedDeriv k f x = 0) : f =ᶠ[𝓝 x] 0 := by
  classical
  cases s with
  | zero => simpa [iteratedDeriv_zero] using he
  | succ r =>
    let U : Fin (r+1) → ℂ → ℂ := fun j => iteratedDeriv j.val f
    let A : Fin (r+1) → Fin (r+1) → ℂ → ℂ := fun j k =>
      if j.val = r then a k else fun _ => if k.val = j.val + 1 then 1 else 0
    have hA (j k : Fin (r+1)) : AnalyticAt ℂ (A j k) x := by
      unfold A
      split
      · exact ha k
      · exact analyticAt_const
    have hSys (j : Fin (r+1)) : ∀ᶠ z in 𝓝 x, deriv (U j) z = ∑ k, A j k z * U k z := by
      by_cases hj : j.val = r
      · simpa only [U, A, hj, if_true, iteratedDeriv_succ] using he
      · have hj' : j.val + 1 < r + 1 := by omega
        let next : Fin (r+1) := ⟨j.val + 1, hj'⟩
        have hnext (k : Fin (r+1)) : k.val = j.val + 1 ↔ k = next := by
          change k.val = next.val ↔ k = next
          exact ⟨Fin.ext, fun e => congrArg Fin.val e⟩
        filter_upwards [] with z
        simp only [U, A, hj, if_false, hnext, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [iteratedDeriv_succ]
    have hU := v5_first_order_zero_of_zero_initial hA
      (fun j => v5_jet_analyticAt hf j.val) hSys (fun j => h0 j.val j.isLt)
      (0 : Fin (r+1))
    simpa [U, iteratedDeriv_zero] using hU

/-- A cleared polynomial operator with nonvanishing leading coefficient at x
has no nonzero analytic solution germ with all its initial jets zero. -/
theorem v5_cleared_scalar_zero_of_zero_jets {K : Type*} [Field K] [Algebra K ℂ]
    {s : ℕ} {f : ℂ → ℂ} {x : ℂ} (a : ℕ → Polynomial K)
    (hlead : (a s).eval₂ (algebraMap K ℂ) x ≠ 0)
    (hf : AnalyticAt ℂ f x) (he : ∀ᶠ z in 𝓝 x, v5RowResidual f s a z = 0)
    (h0 : ∀ k < s, iteratedDeriv k f x = 0) : f =ᶠ[𝓝 x] 0 := by
  let b (i : ℕ) (z : ℂ) := (a i).eval₂ (algebraMap K ℂ) z
  have hb (i : ℕ) : AnalyticAt ℂ (b i) x := by
    change AnalyticAt ℂ (fun z => (a i).eval₂ (algebraMap K ℂ) z) x
    simp_rw [Polynomial.eval₂_eq_eval_map (algebraMap K ℂ)]
    simpa only [Polynomial.aeval_def] using
      (analyticAt_id : AnalyticAt ℂ (fun z : ℂ => z) x).aeval_polynomial
        ((a i).map (algebraMap K ℂ))
  have hn : ∀ᶠ z in 𝓝 x, b s z ≠ 0 :=
    (hb s).continuousAt.eventually_ne hlead
  apply v5_normalized_scalar_zero_of_zero_jets
    (fun j z => -(b j.val z) / b s z)
    (fun j => (hb j.val).neg.div (hb s) hlead) hf ?_ h0
  filter_upwards [he, hn] with z hz hnz
  change (∑ i ∈ Finset.range (s+1), b i z * iteratedDeriv i f z) = 0 at hz
  rw [Finset.sum_range_succ] at hz
  rw [Fin.sum_univ_eq_sum_range (fun i => -(b i z) / b s z * iteratedDeriv i f z)]
  have hsum : (∑ i ∈ Finset.range s, -(b i z) / b s z * iteratedDeriv i f z) =
      -(∑ i ∈ Finset.range s, b i z * iteratedDeriv i f z) / b s z := by
    rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [div_mul_eq_mul_div, neg_mul, neg_div]
  rw [hsum]
  apply (eq_div_iff hnz).2
  linear_combination hz

#print axioms v5_first_order_zero_of_zero_initial
#print axioms v5_normalized_scalar_zero_of_zero_jets
#print axioms v5_cleared_scalar_zero_of_zero_jets
end StrictEUnit
