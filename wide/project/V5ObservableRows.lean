import V5CyclicCoordinateFamily

namespace StrictEUnit
open scoped Topology BigOperators
open Filter

noncomputable def v5ObservableRow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → ℂ → ℂ) (coord : ι) : ℕ → ι → ℂ → ℂ
  | 0, k, _ => if k = coord then 1 else 0
  | n + 1, k, z => deriv (v5ObservableRow A coord n k) z +
      ∑ j, v5ObservableRow A coord n j z * A j k z

theorem v5_observableRow_analyticAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → ι → ℂ → ℂ} {x : ℂ} (hA : ∀ j k, AnalyticAt ℂ (A j k) x)
    (coord : ι) (n : ℕ) (k : ι) : AnalyticAt ℂ (v5ObservableRow A coord n k) x := by
  induction n generalizing k with
  | zero =>
    change AnalyticAt ℂ (fun _ : ℂ => if k = coord then (1 : ℂ) else 0) x
    exact analyticAt_const
  | succ n ih =>
    change AnalyticAt ℂ (fun z => deriv (v5ObservableRow A coord n k) z +
      ∑ j, v5ObservableRow A coord n j z * A j k z) x
    apply (ih k).deriv.add
    exact Finset.analyticAt_sum _ fun j _ => (ih j).mul (hA j k)

private theorem v5_deriv_observable_pairing {ι : Type*} [Fintype ι]
    {r U : ι → ℂ → ℂ} {A : ι → ι → ℂ → ℂ} {x : ℂ}
    (hr : ∀ j, AnalyticAt ℂ (r j) x) (hu : ∀ j, AnalyticAt ℂ (U j) x)
    (hSys : ∀ j, deriv (U j) x = ∑ k, A j k x * U k x) :
    deriv (fun z => ∑ j, r j z * U j z) x =
      ∑ k, (deriv (r k) x + ∑ j, r j x * A j k x) * U k x := by
  classical
  have hd := (HasDerivAt.sum (u := Finset.univ) fun j _ =>
    (hr j).differentiableAt.hasDerivAt.mul (hu j).differentiableAt.hasDerivAt).deriv
  rw [hd]
  simp only [hSys, add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- For a local analytic solution of U'=A U, the n-th derivative of the observed
coordinate is the n-th recurrent row applied to U, on the whole germ. -/
theorem v5_observableRow_iteratedDeriv {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → ι → ℂ → ℂ} {U : ι → ℂ → ℂ} {x : ℂ}
    (hA : ∀ j k, AnalyticAt ℂ (A j k) x) (hu : ∀ j, AnalyticAt ℂ (U j) x)
    (hSys : ∀ j, ∀ᶠ z in 𝓝 x, deriv (U j) z = ∑ k, A j k z * U k z)
    (coord : ι) (n : ℕ) :
    iteratedDeriv n (U coord) =ᶠ[𝓝 x]
      (fun z => ∑ k, v5ObservableRow A coord n k z * U k z) := by
  classical
  have hAe : ∀ᶠ z in 𝓝 x, ∀ j k, AnalyticAt ℂ (A j k) z :=
    Filter.eventually_all.mpr fun j => Filter.eventually_all.mpr fun k =>
      (hA j k).eventually_analyticAt
  have hue : ∀ᶠ z in 𝓝 x, ∀ j, AnalyticAt ℂ (U j) z :=
    Filter.eventually_all.mpr fun j => (hu j).eventually_analyticAt
  have hs : ∀ᶠ z in 𝓝 x, ∀ j, deriv (U j) z = ∑ k, A j k z * U k z :=
    Filter.eventually_all.mpr hSys
  induction n with
  | zero =>
    filter_upwards [] with z
    simp [iteratedDeriv_zero, v5ObservableRow, ite_mul, Finset.sum_ite_eq']
  | succ n ih =>
    rw [iteratedDeriv_succ]
    filter_upwards [ih.deriv, hAe, hue, hs] with z he hAz huz hsz
    rw [he]
    exact v5_deriv_observable_pairing (fun j => v5_observableRow_analyticAt hAz coord n j) huz hsz

/-- Apply the recurrent rows to all normalized analytic columns of the system. -/
theorem v5_cyclic_coordinate_family_from_first_order {d : ℕ} {x : ℂ}
    (A : Fin d → Fin d → ℂ → ℂ) (coord : Fin d) (U : Fin d → Fin d → ℂ → ℂ)
    (hA : ∀ j k, AnalyticAt ℂ (A j k) x)
    (hu : ∀ j k, AnalyticAt ℂ (U j k) x)
    (hinit : ∀ j k, U j k x = if k = j then 1 else 0)
    (hSys : ∀ j k, ∀ᶠ z in 𝓝 x, deriv (U j k) z = ∑ l, A k l z * U j l z)
    (hfull : ∃ᶠ z in 𝓝 x, Function.Injective
      (fun (v : Fin d → ℂ) (i : Fin d) =>
        ∑ k, v5ObservableRow A coord i.val k z * v k)) :
    v5FiniteGermIndependent x (fun j => U j coord) := by
  apply v5_cyclic_coordinate_germ_independent coord U
    (fun i => v5ObservableRow A coord i.val) hu hinit ?_ hfull
  intro j i
  exact v5_observableRow_iteratedDeriv hA (hu j) (hSys j) coord i.val

#print axioms v5_observableRow_iteratedDeriv
#print axioms v5_cyclic_coordinate_family_from_first_order
end StrictEUnit
