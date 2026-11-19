import V5OrdinaryScalarFamily
import V5ScalarJetTransport
import ArbitraryActualOrdinaryGerms
import OrdinaryAnalyticODETransfer
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

noncomputable section
open scoped Topology BigOperators Matrix
open Filter
namespace StrictEUnit

def v5AnalyticJetMatrix {n : ℕ} (u : Fin n → ℂ → ℂ) (z : ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => iteratedDeriv i.val (u j) z

def v5FormalJetMatrix {n : ℕ} (s : Fin n → PowerSeries ℂ) :
    Matrix (Fin n) (Fin n) (PowerSeries ℂ) :=
  fun i j => (PowerSeries.derivative ℂ)^[i.val] (s j)

/-- Full analytic germ independence forces nonzero jet determinant at every
nearby ordinary point; the center itself may remain an apparent singularity. -/
theorem v5_analytic_jet_det_frequently_ne_zero {n : ℕ} {x : ℂ}
    (p : ℕ → Polynomial ℂ) (hp : p n ≠ 0) (u : Fin n → ℂ → ℂ)
    (hu : ∀ i, AnalyticAt ℂ (u i) x) (hi : v5FiniteGermIndependent x u)
    (he : ∀ i, ∀ᶠ z in 𝓝 x, v5RowResidual (u i) n p z = 0) :
    ∃ᶠ z in 𝓝 x, (v5AnalyticJetMatrix u z).det ≠ 0 := by
  classical
  obtain ⟨D,ho,hcon,hx,hU,hODE⟩ := v5_scalar_family_common_ball p u hu he
  have hDx := ho.mem_nhds hx
  have hfreq := mem_closure_iff_frequently.mp ((v5_dense_polynomial_eval_ne_zero (p n) hp) x)
  apply (hfreq.and_eventually (show ∀ᶠ y in 𝓝 x, y ∈ D from hDx)).mono
  intro y ⟨hy,hDy⟩ hzero
  obtain ⟨c,hc,hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hzero
  have hm : v5FactorInitialJetMap n u y c = 0 := by
    funext i
    have h := congrFun hker i
    change (∑ j, iteratedDeriv i.val (u j) y * c j) = 0 at h
    change (∑ j, c j * iteratedDeriv i.val (u j) y) = 0
    simpa only [mul_comm] using h
  have hUa : AnalyticOnNhd ℂ (v5WeightedGerm u c) D := by
    intro z hz
    exact Finset.analyticAt_sum _ fun j _ => analyticAt_const.mul (hU j z hz)
  have hE : ∀ᶠ z in 𝓝 y, v5RowResidual (v5WeightedGerm u c) n p z = 0 := by
    filter_upwards [show ∀ᶠ z in 𝓝 y, z ∈ D from ho.mem_nhds hDy] with z hz
    rw [v5_rowResidual_weightedGerm (fun j => hU j z hz)]
    simp [v5WeightedGerm, hODE _ z hz]
  have hz := v5_cleared_scalar_zero_of_zero_jets p hy (hUa y hDy) hE
    ((v5_initialJetMap_eq_zero_iff (fun j => hU j y hDy) c).mp hm)
  have hmark : v5WeightedGerm u c =ᶠ[𝓝 x] 0 :=
    (Filter.eventually_of_mem hDx)
      (hUa.eqOn_zero_of_preconnected_of_eventuallyEq_zero hcon hDy hz)
  apply hc
  funext j
  exact hi c hmark j

private theorem v5_hasSeries_const (c : ℂ) :
    HasFPowerSeriesAt (fun _ : ℂ => c)
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => PowerSeries.coeff ℂ n (PowerSeries.C ℂ c))) 0 := by
  simpa only [Polynomial.eval_C, Polynomial.coe_C] using
    hasFPowerSeriesAt_polynomial_ofScalars (Polynomial.C c)

private theorem v5_hasSeries_finset_prod {ι : Type*} (s : Finset ι)
    (f : ι → ℂ → ℂ) (a : ι → PowerSeries ℂ)
    (h : ∀ i ∈ s, HasFPowerSeriesAt (f i)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n (a i))) 0) :
    HasFPowerSeriesAt (fun z => ∏ i ∈ s, f i z)
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => PowerSeries.coeff ℂ n (∏ i ∈ s, a i))) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, map_one] using v5_hasSeries_const 1
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using
      hasFPowerSeriesAt_mul_ofScalars (f i) (fun z => ∏ j ∈ s, f j z)
        (a i) (∏ j ∈ s, a j) (h i (Finset.mem_insert_self i s))
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem v5_formal_jet_det_realizes {n : ℕ} (u : Fin n → ℂ → ℂ)
    (s : Fin n → PowerSeries ℂ)
    (hs : ∀ i, HasFPowerSeriesAt (u i)
      (FormalMultilinearSeries.ofScalars ℂ (fun k => PowerSeries.coeff ℂ k (s i))) 0) :
    HasFPowerSeriesAt (fun z => (v5AnalyticJetMatrix u z).det)
      (FormalMultilinearSeries.ofScalars ℂ
        (fun k => PowerSeries.coeff ℂ k (v5FormalJetMatrix s).det)) 0 := by
  classical
  simp only [Matrix.det_apply']
  apply hasFPowerSeriesAt_finset_sum_ofScalars Finset.univ
  intro σ _
  let c : ℂ := ((Equiv.Perm.sign σ : ℤˣ) : ℤ)
  have hprod := v5_hasSeries_finset_prod Finset.univ
    (fun j z => iteratedDeriv (σ j).val (u j) z)
    (fun j => (PowerSeries.derivative ℂ)^[(σ j).val] (s j))
    (fun j _ => hasFPowerSeriesAt_iteratedDeriv_ofScalars _ _ (hs j) (σ j).val)
  have h := hasFPowerSeriesAt_mul_ofScalars (fun _ => c) _ (PowerSeries.C ℂ c) _
    (v5_hasSeries_const c) hprod
  have he : PowerSeries.C ℂ c = (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : PowerSeries ℂ) := by
    simp only [c,map_intCast]
  rw [he] at h
  exact h

/-- A nearby nonzero Wronskian gives a genuinely nonzero formal jet
determinant even when its constant coefficient is zero. -/
theorem v5_formal_jet_det_ne_zero_from_analytic {n : ℕ} (u : Fin n → ℂ → ℂ)
    (s : Fin n → PowerSeries ℂ)
    (hs : ∀ i, HasFPowerSeriesAt (u i)
      (FormalMultilinearSeries.ofScalars ℂ (fun k => PowerSeries.coeff ℂ k (s i))) 0)
    (hf : ∃ᶠ z in 𝓝 (0:ℂ), (v5AnalyticJetMatrix u z).det ≠ 0) :
    (v5FormalJetMatrix s).det ≠ 0 := by
  intro hz
  have h := v5_formal_jet_det_realizes u s hs
  rw [hz] at h
  have he : (fun k => PowerSeries.coeff ℂ k (0 : PowerSeries ℂ)) = (0 : ℕ → ℂ) := by
    funext k
    exact map_zero (PowerSeries.coeff ℂ k)
  rw [he, FormalMultilinearSeries.ofScalars_series_eq_zero_of_scalar_zero] at h
  exact hf (h.eventually_eq_zero.mono (fun _ heq => not_not_intro heq))

/-- The exact local analytic scalar equation gives the corresponding formal
scalar polynomial equation for the same Taylor series. -/
theorem v5_formal_ode_from_analytic_germ {n : ℕ} (p : ℕ → Polynomial ℂ)
    (f : ℂ → ℂ) (s : PowerSeries ℂ)
    (hs : HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars ℂ (fun k => PowerSeries.coeff ℂ k s)) 0)
    (he : ∀ᶠ z in 𝓝 (0 : ℂ), v5RowResidual f n p z = 0) :
    v5ScalarODE p (n+1) s = 0 := by
  have H := hasFPowerSeriesAt_finset_sum_ofScalars (Finset.range (n+1))
    (fun j z => (p j).eval z * iteratedDeriv j f z)
    (fun j => (p j : PowerSeries ℂ) * (PowerSeries.derivative ℂ)^[j] s)
    (fun j _ => hasFPowerSeriesAt_mul_ofScalars _ _ _ _
      (hasFPowerSeriesAt_polynomial_ofScalars (p j))
      (hasFPowerSeriesAt_iteratedDeriv_ofScalars _ _ hs j))
  have H0 : HasFPowerSeriesAt (fun _ : ℂ => (0:ℂ))
      (FormalMultilinearSeries.ofScalars ℂ
        (fun k => PowerSeries.coeff ℂ k (0:PowerSeries ℂ))) 0 := by
    simpa only [map_zero] using v5_hasSeries_const 0
  exact ordinary_series_eq_of_eventually _ _ _ _ H H0 he

#print axioms v5_analytic_jet_det_frequently_ne_zero
#print axioms v5_formal_jet_det_realizes
#print axioms v5_formal_jet_det_ne_zero_from_analytic
#print axioms v5_formal_ode_from_analytic_germ
end StrictEUnit
end
