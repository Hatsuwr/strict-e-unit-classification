import OrdinaryAnalyticODETransfer
import SelectedTranslatedScalarFamily
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.Shift

noncomputable section
open scoped Topology BigOperators Matrix
namespace StrictEUnit

/-- Independence concerns germs, so a relation is only assumed locally. -/
def IndependentAnalyticGermsAt {r : ℕ} (β : ℂ) (f : Fin r → ℂ → ℂ) : Prop :=
  ∀ c : Fin r → ℂ, (∀ᶠ z in nhds β, (∑ j,c j*f j z)=0) → ∀ j,c j=0

theorem analytic_germs_independent_of_formal {r : ℕ}
    (f : Fin r → ℂ → ℂ) (P : Fin r → PowerSeries ℂ)
    (hf : ∀ j, HasFPowerSeriesAt (f j)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n (P j))) 0)
    (hLI : LinearIndependent ℂ P) : IndependentAnalyticGermsAt 0 f := by
  classical
  intro c hc
  have hs := hasFPowerSeriesAt_finset_sum_ofScalars Finset.univ
    (fun j z => c j*f j z) (fun j => PowerSeries.C ℂ (c j)*P j)
    (fun j hj => hasFPowerSeriesAt_mul_ofScalars _ _ _ _
      (by simpa only [Polynomial.eval_C,Polynomial.coe_C] using
        hasFPowerSeriesAt_polynomial_ofScalars (Polynomial.C (c j))) (hf j))
  have he := hs.eq_zero_of_eventually hc
  have hP : (∑ j,PowerSeries.C ℂ (c j)*P j)=0 := by
    ext n
    have hn := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) he
    simp only [FormalMultilinearSeries.coeff_ofScalars] at hn
    change PowerSeries.coeff ℂ n (∑ j,PowerSeries.C ℂ (c j)*P j)=0 at hn
    simpa only [map_zero] using hn
  have hlin : (∑ j,c j • P j)=0 := by
    simpa only [PowerSeries.smul_eq_C_mul] using hP
  exact Fintype.linearIndependent_iff.1 hLI c hlin

theorem iteratedDeriv_comp_sub_const (f : ℂ → ℂ) (β : ℂ) (n : ℕ) :
    iteratedDeriv n (fun z => f (z-β)) = fun z => iteratedDeriv n f (z-β) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext z
    rw [deriv_comp_sub_const,iteratedDeriv_succ]

theorem independentAnalyticGermsAt_comp_sub {r : ℕ}
    (f : Fin r → ℂ → ℂ) (h : IndependentAnalyticGermsAt 0 f) (β : ℂ) :
    IndependentAnalyticGermsAt β (fun j z => f j (z-β)) := by
  intro c hc
  have ht : Filter.Tendsto (fun z : ℂ => z+β) (nhds 0) (nhds β) := by
    have hct : ContinuousAt (fun z : ℂ => z+β) 0 :=
      continuousAt_id.add continuousAt_const
    simpa only [zero_add] using hct.tendsto
  have hh := ht.eventually hc
  apply h c
  simpa only [add_sub_cancel_right] using hh

theorem polynomial_shift_map_eval_sub
    {K : Type*} [Field K] (σ : K →+* ℂ) (p : Polynomial K) (α : K) (z : ℂ) :
    ((p.comp (Polynomial.X+Polynomial.C α)).map σ).eval (z-σ α) = (p.map σ).eval z := by
  rw [Polynomial.eval_map,Polynomial.eval₂_comp]
  simp only [Polynomial.eval₂_add,Polynomial.eval₂_X,Polynomial.eval₂_C,sub_add_cancel]
  rw [Polynomial.eval_map]

/-- Actual local scalar solutions of the literal ORIGINAL selected operator
at the supplied ordinary center, with the exact convergent Taylor coefficients.
This is a starting germ family; continuation to singular zero is separate. -/
theorem ordinaryPoint_actual_scalar_germs
    {K : Type*} [Field K] [NumberField K]
    (r : ℕ) (hr : 0 < r) (c : Fin r → RatFunc K)
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (hclear : ∀ i l, algebraMap (Polynomial K) (RatFunc K) (U i l) =
      algebraMap (Polynomial K) (RatFunc K) t * minimalDerivativeCompanion r c i l)
    (α : K) (hα : t.eval α ≠ 0) (σ : K →+* ℂ) :
    let Z := formalFundamentalMatrix (ordinaryPointClearedMatrix t U α)
    let f : Fin r → ℂ → ℂ := fun j => ordinaryPointAnalyticMatrix σ t U α ⟨0,hr⟩ j
    let g : Fin r → ℂ → ℂ := fun j z => f j (z-σ α)
    let q := sameCompanionScalarTuple r hr t U
    ∃ C : ℝ, ∃ hC : 1 ≤ C,
      (∀ j, HasFPowerSeriesOnBall (g j)
        (FormalMultilinearSeries.ofScalars ℂ
          (fun n => σ (PowerSeries.coeff K n (Z ⟨0,hr⟩ j))))
        (σ α) (ordinaryGermRadius C hC : ENNReal)) ∧
      IndependentAnalyticGermsAt (σ α) g ∧
      ∀ᶠ z in nhds (σ α), ∀ j,
        (∑ i, ((q i).map σ).eval z * iteratedDeriv i.val (g j) z)=0 := by
  classical
  let Z := formalFundamentalMatrix (ordinaryPointClearedMatrix t U α)
  let P : Fin r → PowerSeries ℂ := fun j => PowerSeries.map σ (Z ⟨0,hr⟩ j)
  let f : Fin r → ℂ → ℂ := fun j => ordinaryPointAnalyticMatrix σ t U α ⟨0,hr⟩ j
  let g : Fin r → ℂ → ℂ := fun j z => f j (z-σ α)
  let q := sameCompanionScalarTuple r hr t U
  obtain ⟨C,hC,hOn⟩ := ordinaryPoint_fundamental_analytic_germs t U α hα σ
  have hAt : ∀ j, HasFPowerSeriesAt (f j)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n (P j))) 0 := by
    intro j
    simpa only [P,PowerSeries.coeff_map] using (hOn ⟨0,hr⟩ j).hasFPowerSeriesAt
  obtain ⟨hjets,hLIK,hLIC,hscalarK,hscalarC⟩ :=
    ordinaryPoint_companion_translated_scalar_family r hr c t U hclear α hα σ
  refine ⟨C,hC,?_,?_,?_⟩
  · intro j
    simpa only [zero_add] using (hOn ⟨0,hr⟩ j).comp_sub (σ α)
  · exact independentAnalyticGermsAt_comp_sub f
      (analytic_germs_independent_of_formal f P hAt hLIC) (σ α)
  · have hloc : ∀ᶠ z in nhds (0:ℂ), ∀ j,
        (∑ i, (((q i).comp (Polynomial.X+Polynomial.C α)).map σ).eval z *
          iteratedDeriv i.val (f j) z)=0 := by
      apply Filter.eventually_all.2
      intro j
      exact ordinary_series_scalar_ode_eventually (f j) (P j) (r+1)
        (fun i => ((q i).comp (Polynomial.X+Polynomial.C α)).map σ)
        (hAt j) (hscalarC j)
    have ht : Filter.Tendsto (fun z : ℂ => z-σ α) (nhds (σ α)) (nhds 0) := by
      have hct : ContinuousAt (fun z : ℂ => z-σ α) (σ α) :=
        continuousAt_id.sub continuousAt_const
      simpa only [sub_self] using hct.tendsto
    filter_upwards [ht.eventually hloc] with z hz
    intro j
    have hj := hz j
    simp only [polynomial_shift_map_eval_sub] at hj
    simpa only [g,iteratedDeriv_comp_sub_const] using hj

end StrictEUnit
end
