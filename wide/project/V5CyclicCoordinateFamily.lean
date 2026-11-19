import V5NormVanishingBasis

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

/-- The observable jet rows recover the vector near the mark wherever they have
full rank. The rows are not required to have full rank at the mark itself. -/
theorem v5_cyclic_coordinate_germ_independent {d : ℕ} {x : ℂ}
    (coord : Fin d) (U : Fin d → Fin d → ℂ → ℂ)
    (R : Fin d → Fin d → ℂ → ℂ)
    (hu : ∀ j k, AnalyticAt ℂ (U j k) x)
    (hinit : ∀ j k, U j k x = if k = j then 1 else 0)
    (hjet : ∀ j i, ∀ᶠ z in 𝓝 x, iteratedDeriv i.val (U j coord) z =
      ∑ k, R i k z * U j k z)
    (hfull : ∃ᶠ z in 𝓝 x, Function.Injective
      (fun (v : Fin d → ℂ) (i : Fin d) => ∑ k, R i k z * v k)) :
    v5FiniteGermIndependent x (fun j => U j coord) := by
  classical
  intro c hc
  let F : Fin d → ℂ → ℂ := fun k z => ∑ j, c j * U j k z
  have hAll : ∀ᶠ z in 𝓝 x, ∀ j i, AnalyticAt ℂ (U j coord) z ∧
      iteratedDeriv i.val (U j coord) z = ∑ k, R i k z * U j k z :=
    Filter.eventually_all.mpr fun j => Filter.eventually_all.mpr fun i =>
      ((hu j coord).eventually_analyticAt).and (hjet j i)
  have hobs : ∀ᶠ z in 𝓝 x, ∀ i, (∑ k, R i k z * F k z) = 0 := by
    filter_upwards [hc.eventually_nhds, hAll] with z hz hzis i
    have hzero : iteratedDeriv i.val (F coord) z = 0 := by
      have he : F coord =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := hz
      simpa only [v5_iteratedDeriv_zero_fun] using he.iteratedDeriv_eq i.val
    rw [v5_iteratedDeriv_finite_weighted_sum i.val c Finset.univ
      (fun j => (hzis j i).1)] at hzero
    simp only [fun j => (hzis j i).2, Finset.mul_sum] at hzero
    unfold F
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    convert hzero using 1
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hfzero : ∃ᶠ z in 𝓝 x, ∀ k, F k z = 0 :=
    (hfull.and_eventually hobs).mono fun z ⟨hz, hzero⟩ => by
      have he : (fun k => F k z) = (fun _ => (0 : ℂ)) := by
        apply hz
        funext i
        simpa only [mul_zero, Finset.sum_const_zero] using hzero i
      exact congrFun he
  intro k
  have hcont : ContinuousAt (F k) x := by
    unfold F
    apply tendsto_finset_sum
    intro j _
    exact continuousAt_const.mul (hu j k).continuousAt
  have h0 : F k x = 0 :=
    tendsto_nhds_unique_of_frequently_eq hcont tendsto_const_nhds
      (hfzero.mono fun _ h => h k)
  have he : F k x = c k := by
    simp [F, hinit, mul_ite, Finset.sum_ite_eq]
  exact he ▸ h0

/-- A nonzero polynomial certificate for rank away from its roots is enough. -/
theorem v5_cyclic_coordinate_germ_independent_of_rank_certificate
    {K : Type*} [Field K] [Algebra K ℂ] {d : ℕ} {x : ℂ}
    (coord : Fin d) (U R : Fin d → Fin d → ℂ → ℂ)
    (hu : ∀ j k, AnalyticAt ℂ (U j k) x)
    (hinit : ∀ j k, U j k x = if k = j then 1 else 0)
    (hjet : ∀ j i, ∀ᶠ z in 𝓝 x, iteratedDeriv i.val (U j coord) z =
      ∑ k, R i k z * U j k z)
    (p : Polynomial K) (hp : p ≠ 0)
    (hrank : ∀ᶠ z in 𝓝 x, (Polynomial.eval₂RingHom (algebraMap K ℂ) z) p ≠ 0 →
      Function.Injective (fun (v : Fin d → ℂ) (i : Fin d) => ∑ k, R i k z * v k)) :
    v5FiniteGermIndependent x (fun j => U j coord) := by
  apply v5_cyclic_coordinate_germ_independent coord U R hu hinit hjet
  exact ((mem_closure_iff_frequently.mp ((v5_dense_polynomial_eval_ne_zero p hp) x)).and_eventually
    hrank).mono fun _ ⟨hnz, h⟩ => h hnz

#print axioms v5_cyclic_coordinate_germ_independent
#print axioms v5_cyclic_coordinate_germ_independent_of_rank_certificate
end StrictEUnit
