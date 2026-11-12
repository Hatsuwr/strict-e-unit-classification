import ComplexCompactOrdinaryBounds
import ComplexOriginalCoordinateGerms

noncomputable section
open scoped Topology BigOperators Matrix
namespace StrictEUnit

theorem analytic_vector_cleared_ode_on_preconnected {r : ℕ}
    (s : Set ℂ) (hs : IsPreconnected s) (h0 : (0:ℂ) ∈ s)
    (t : Polynomial ℂ) (U : Matrix (Fin r) (Fin r) (Polynomial ℂ))
    (F : Fin r → ℂ → ℂ) (hF : ∀ i,AnalyticOnNhd ℂ (F i) s)
    (hlocal : ∀ᶠ z in nhds (0:ℂ), ∀ i,
      t.eval z*deriv (F i) z=∑ l,(U i l).eval z*F l z) :
    ∀ z ∈ s, ∀ i,t.eval z*deriv (F i) z=∑ l,(U i l).eval z*F l z := by
  intro z hz i
  have hp (P : Polynomial ℂ) : AnalyticOnNhd ℂ (fun z => P.eval z) s :=
    (AnalyticOnNhd.eval_polynomial (𝕜:=ℂ) P).mono (Set.subset_univ s)
  have hl := (hp t).mul (hF i).deriv
  have hr := Finset.univ.analyticOnNhd_sum (fun l _ => (hp (U i l)).mul (hF l))
  exact (hl.eqOn_of_preconnected_of_eventuallyEq hr hs h0
    (hlocal.mono (fun z hz => hz i))) hz

/-- Every arbitrary analytic solution germ at every center of a compact
regular set extends to ONE common positive disk. Neither the center nor the
initial values are restricted to algebraic numbers. -/
theorem complexOrdinaryPoint_uniform_germ_disks_on_compact {r : ℕ}
    (t : Polynomial ℂ) (U : Matrix (Fin r) (Fin r) (Polynomial ℂ))
    (s : Set ℂ) (hcompact : IsCompact s) (hs : ∀ β ∈ s,t.eval β ≠ 0) :
    ∃ M : ℝ,∃ hM : 1 ≤ M, ∀ β ∈ s, ∀ f : Fin r → ℂ → ℂ,
      ClearedAnalyticSolutionGermAt (ordinaryPointPolynomialShift β t)
        (fun i l => ordinaryPointPolynomialShift β (U i l)) 0 f →
      ∃ F : Fin r → ℂ → ℂ,
        ClearedAnalyticSolutionOn (ordinaryPointPolynomialShift β t)
          (fun i l => ordinaryPointPolynomialShift β (U i l))
          (EMetric.ball 0 (ordinaryGermRadius M hM : ENNReal)) F ∧
        ∀ᶠ z in nhds (0:ℂ), ∀ i,f i z=F i z := by
  classical
  obtain ⟨M,hM,hOn⟩ := complexOrdinaryPoint_uniform_analytic_disks_on_compact t U s hcompact hs
  refine ⟨M,hM,?_⟩
  intro β hβ f hf
  let F : Fin r → ℂ → ℂ := fun i z => ∑ j,complexOrdinaryAnalyticMatrix t U β i j z*f j 0
  have hF i : AnalyticOnNhd ℂ (F i) (EMetric.ball 0 (ordinaryGermRadius M hM : ENNReal)) :=
    Finset.univ.analyticOnNhd_sum (fun j _ => ((hOn β hβ i j).analyticOnNhd).mul analyticOnNhd_const)
  have heq := complexOrdinaryPoint_arbitrary_actual_germ_representation t U β (hs β hβ) f hf.1 hf.2
  obtain ⟨C,hC,hall⟩ := complexOrdinaryPoint_all_initial_values_on_disk t U β (hs β hβ)
  obtain ⟨hFa,hF0,hFode⟩ := hall (fun j => f j 0)
  have hCpos : (0:ENNReal)<(ordinaryGermRadius C hC : ENNReal) := by
    exact_mod_cast ordinaryGermRadius_pos C hC
  have hlocal : ∀ᶠ z in nhds (0:ℂ), ∀ i,
      (ordinaryPointPolynomialShift β t).eval z*deriv (F i) z=
        ∑ l,(ordinaryPointPolynomialShift β (U i l)).eval z*F l z := by
    filter_upwards [EMetric.ball_mem_nhds (0:ℂ) hCpos] with z hz
    exact hFode z hz
  have hMpos : (0:ENNReal)<(ordinaryGermRadius M hM : ENNReal) := by
    exact_mod_cast ordinaryGermRadius_pos M hM
  exact ⟨F,⟨hF,analytic_vector_cleared_ode_on_preconnected _
    (Metric.isConnected_eball hMpos).isPreconnected (EMetric.mem_ball_self hMpos)
    _ _ F hF hlocal⟩,heq⟩

/-- Uniform disks for arbitrary germs in the literal ORIGINAL coordinate.
This is the local existence/uniqueness input for a finite regular-path chain. -/
theorem complexOriginalCenter_uniform_germ_disks_on_compact {r : ℕ}
    (t : Polynomial ℂ) (U : Matrix (Fin r) (Fin r) (Polynomial ℂ))
    (s : Set ℂ) (hcompact : IsCompact s) (hs : ∀ β ∈ s,t.eval β ≠ 0) :
    ∃ M : ℝ,∃ hM : 1 ≤ M, ∀ β ∈ s, ∀ f : Fin r → ℂ → ℂ,
      ClearedAnalyticSolutionGermAt t U β f →
      ∃ F : Fin r → ℂ → ℂ,
        ClearedAnalyticSolutionOn t U
          (EMetric.ball β (ordinaryGermRadius M hM : ENNReal)) F ∧
        ∀ᶠ z in nhds β, ∀ i,f i z=F i z := by
  obtain ⟨M,hM,hext⟩ := complexOrdinaryPoint_uniform_germ_disks_on_compact t U s hcompact hs
  refine ⟨M,hM,?_⟩
  intro β hβ f hf
  have ht := clearedAnalyticSolutionGermAt_translate t U β f hf
  obtain ⟨G,⟨hG,hode⟩,heq⟩ := hext β hβ (fun i z => f i (z+β)) ht
  let F : Fin r → ℂ → ℂ := fun i z => G i (z-β)
  have hmem (z : ℂ) (hz : z ∈ EMetric.ball β (ordinaryGermRadius M hM : ENNReal)) :
      z-β ∈ EMetric.ball 0 (ordinaryGermRadius M hM : ENNReal) := by
    simpa only [EMetric.mem_ball,edist_eq_enorm_sub,sub_zero] using hz
  refine ⟨F,⟨?_,?_⟩,?_⟩
  · intro i z hz
    change AnalyticAt ℂ (fun w : ℂ => G i (w-β)) z
    have ha : AnalyticAt ℂ (fun w : ℂ => w-β) z := analyticAt_id.sub analyticAt_const
    exact (hG i (z-β) (hmem z hz)).comp (f:=fun w : ℂ => w-β) (x:=z) ha
  · intro z hz i
    have hi := hode (z-β) (hmem z hz) i
    simp only [ordinaryPointPolynomialShift_eval_complex,sub_add_cancel] at hi
    simpa only [F,deriv_comp_sub_const] using hi
  · have hn : Filter.Tendsto (fun z : ℂ => z-β) (nhds β) (nhds 0) := by
      have hc : ContinuousAt (fun z : ℂ => z-β) β := continuousAt_id.sub continuousAt_const
      simpa only [sub_self] using hc.tendsto
    filter_upwards [hn.eventually heq] with z hz
    simpa only [sub_add_cancel,F] using hz

end StrictEUnit
end
