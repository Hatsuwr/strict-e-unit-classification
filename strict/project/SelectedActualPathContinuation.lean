import ComplexRegularPathContinuation
import Stage41SameSelectedActualAnalyticGerms

noncomputable section
open scoped Topology BigOperators Matrix NumberField unitInterval
namespace StrictEUnit

/-- Actual regular-path continuation, with finite disk-chain witnesses and
literal original-coordinate equations. The starting germ is arbitrary. -/
def RegularPathContinuationAt {r : ℕ} (t : Polynomial ℂ)
    (U : Matrix (Fin r) (Fin r) (Polynomial ℂ)) (β : ℂ) : Prop :=
  ∀ γ : unitInterval → ℂ,Continuous γ → γ 0=β →
    (∀ q,t.eval (γ q) ≠ 0) → ∀ f : Fin r → ℂ → ℂ,
    ClearedAnalyticSolutionGermAt t U β f →
    ∃ R : NNReal,0<R ∧ ∃ τ : ℕ → unitInterval,
      τ 0=0 ∧ Monotone τ ∧ (∃ N,∀ n ≥ N,τ n=1) ∧
      (∀ n q,q ∈ Set.Icc (τ n) (τ (n+1)) → γ q ∈ EMetric.ball (γ (τ n)) (R:ENNReal)) ∧
      ∃ F : ℕ → Fin r → ℂ → ℂ,
        (∀ n,ClearedAnalyticSolutionOn t U (EMetric.ball (γ (τ n)) (R:ENNReal)) (F n)) ∧
        (∀ᶠ z in nhds β,∀ i,f i z=F 0 i z) ∧
        ∀ n,∀ᶠ z in nhds (γ (τ (n+1))),∀ i,F n i z=F (n+1) i z

theorem polynomial_system_regularPathContinuationAt {r : ℕ} (t : Polynomial ℂ)
    (U : Matrix (Fin r) (Fin r) (Polynomial ℂ)) (β : ℂ) :
    RegularPathContinuationAt t U β := by
  intro γ hγ hstart hregular f hf
  have h := complex_regular_path_actual_germ_continuation t U γ hγ hregular f
    (by simpa only [hstart] using hf)
  simpa only [hstart] using h

/-- The actual selected frame columns are starting germs of the literal SAME
original-coordinate cleared system, so the regular-path theorem applies to
them directly. No rational-input transport substitutes for these germs. -/
theorem ordinaryPoint_actual_original_system_germs
    {K : Type*} [Field K] [NumberField K] {r : ℕ}
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K)) (α : K)
    (hα : t.eval α ≠ 0) (χ : K →+* ℂ) (j : Fin r) :
    ClearedAnalyticSolutionGermAt (t.map χ) (fun i l => (U i l).map χ) (χ α)
      (fun i z => ordinaryPointAnalyticMatrix χ t U α i j (z-χ α)) := by
  obtain ⟨C,hC,hOn,h0,hode⟩ := ordinaryPoint_actual_cleared_system t U α hα χ
  constructor
  · intro i
    have ha := (hOn i j).comp_sub (χ α)
    simpa only [zero_add] using ha.hasFPowerSeriesAt.analyticAt
  · have hn : Filter.Tendsto (fun z : ℂ => z-χ α) (nhds (χ α)) (nhds 0) := by
      have hc : ContinuousAt (fun z : ℂ => z-χ α) (χ α) := continuousAt_id.sub continuousAt_const
      simpa only [sub_self] using hc.tendsto
    filter_upwards [hn.eventually hode] with z hz
    intro i
    have hi := hz i j
    have he (p : Polynomial K) : (ordinaryPointPolynomialShift α p).eval₂ χ (z-χ α)=
        (p.map χ).eval z := by
      simpa only [← Polynomial.eval_map,ordinaryPointPolynomialShift_apply] using
        polynomial_shift_map_eval_sub χ p α z
    simp only [he] at hi
    simpa only [deriv_comp_sub_const] using hi

def SameClearingRegularPathContinuationData
    {K : Type*} [Field K] [NumberField K] {r : ℕ}
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin r) (Fin r) (Polynomial (𝓞 K))) : Prop :=
  ∀ χ : K →+* ℂ,∀ β : ℂ,RegularPathContinuationAt
    ((T.map (algebraMap (𝓞 K) K)).map χ)
    (fun i l => ((UI i l).map (algebraMap (𝓞 K) K)).map χ) β

theorem sameClearing_regularPathContinuationData
    {K : Type*} [Field K] [NumberField K] {r : ℕ}
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin r) (Fin r) (Polynomial (𝓞 K))) :
    SameClearingRegularPathContinuationData T UI := by
  intro χ β
  exact polynomial_system_regularPathContinuationAt _ _ β

end StrictEUnit
end
