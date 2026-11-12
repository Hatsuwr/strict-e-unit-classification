import ComplexOrdinaryGermExtension
import Mathlib.Analysis.Calculus.Deriv.Shift

noncomputable section
open scoped Topology BigOperators Matrix
namespace StrictEUnit

def ClearedAnalyticSolutionGermAt {r : ℕ} (t : Polynomial ℂ)
    (U : Matrix (Fin r) (Fin r) (Polynomial ℂ)) (β : ℂ)
    (f : Fin r → ℂ → ℂ) : Prop :=
  (∀ i,AnalyticAt ℂ (f i) β) ∧
  ∀ᶠ z in nhds β, ∀ i,t.eval z*deriv (f i) z=∑ l,(U i l).eval z*f l z

def ClearedAnalyticSolutionOn {r : ℕ} (t : Polynomial ℂ)
    (U : Matrix (Fin r) (Fin r) (Polynomial ℂ)) (s : Set ℂ)
    (f : Fin r → ℂ → ℂ) : Prop :=
  (∀ i,AnalyticOnNhd ℂ (f i) s) ∧
  ∀ z ∈ s, ∀ i,t.eval z*deriv (f i) z=∑ l,(U i l).eval z*f l z

theorem ordinaryPointPolynomialShift_eval_complex (p : Polynomial ℂ) (β z : ℂ) :
    (ordinaryPointPolynomialShift β p).eval z=p.eval (z+β) := by
  rw [ordinaryPointPolynomialShift_apply,Polynomial.eval_comp]
  simp

theorem clearedAnalyticSolutionGermAt_translate {r : ℕ} (t : Polynomial ℂ)
    (U : Matrix (Fin r) (Fin r) (Polynomial ℂ)) (β : ℂ)
    (f : Fin r → ℂ → ℂ) (hf : ClearedAnalyticSolutionGermAt t U β f) :
    ClearedAnalyticSolutionGermAt (ordinaryPointPolynomialShift β t)
      (fun i l => ordinaryPointPolynomialShift β (U i l)) 0
      (fun i z => f i (z+β)) := by
  constructor
  · intro i
    have ha : AnalyticAt ℂ (fun z : ℂ => z+β) 0 := analyticAt_id.add analyticAt_const
    exact (hf.1 i).comp_of_eq ha (zero_add β)
  · have ht : Filter.Tendsto (fun z : ℂ => z+β) (nhds 0) (nhds β) := by
      have hc : ContinuousAt (fun z : ℂ => z+β) 0 := continuousAt_id.add continuousAt_const
      simpa only [zero_add] using hc.tendsto
    filter_upwards [ht.eventually hf.2] with z hz
    intro i
    simpa only [ordinaryPointPolynomialShift_eval_complex,deriv_comp_add_const] using hz i

/-- Arbitrary actual solution germs extend on a disk in the ORIGINAL complex
coordinate at ANY regular complex center. The literal t/U are unchanged. -/
theorem complexOriginalCenter_arbitrary_germ_disk_extension {r : ℕ}
    (t : Polynomial ℂ) (U : Matrix (Fin r) (Fin r) (Polynomial ℂ)) (β : ℂ)
    (hβ : t.eval β ≠ 0) :
    ∃ C : ℝ,∃ hC : 1 ≤ C, ∀ f : Fin r → ℂ → ℂ,
      ClearedAnalyticSolutionGermAt t U β f →
      ∃ F : Fin r → ℂ → ℂ,
        ClearedAnalyticSolutionOn t U
          (EMetric.ball β (ordinaryGermRadius C hC : ENNReal)) F ∧
        ∀ᶠ z in nhds β, ∀ i,f i z=F i z := by
  obtain ⟨C,hC,hext⟩ := complexOrdinaryPoint_arbitrary_actual_germ_disk_extension t U β hβ
  refine ⟨C,hC,?_⟩
  intro f hf
  have ht := clearedAnalyticSolutionGermAt_translate t U β f hf
  obtain ⟨G,hG,heq,hode⟩ := hext (fun i z => f i (z+β)) ht.1 ht.2
  let F : Fin r → ℂ → ℂ := fun i z => G i (z-β)
  have hmem (z : ℂ) (hz : z ∈ EMetric.ball β (ordinaryGermRadius C hC : ENNReal)) :
      z-β ∈ EMetric.ball 0 (ordinaryGermRadius C hC : ENNReal) := by
    simpa only [EMetric.mem_ball,edist_eq_enorm_sub,sub_zero] using hz
  refine ⟨F,⟨?_,?_⟩,?_⟩
  · intro i z hz
    change AnalyticAt ℂ (fun w : ℂ => G i (w-β)) z
    have ha : AnalyticAt ℂ (fun w : ℂ => w-β) z := analyticAt_id.sub analyticAt_const
    exact (hG i (z-β) (hmem z hz)).comp
      (f:=fun w : ℂ => w-β) (x:=z) ha
  · intro z hz i
    have hi := hode (z-β) (hmem z hz) i
    simp only [ordinaryPointPolynomialShift_eval_complex,sub_add_cancel] at hi
    simpa only [F,deriv_comp_sub_const] using hi
  · have hn : Filter.Tendsto (fun z : ℂ => z-β) (nhds β) (nhds 0) := by
      have hc : ContinuousAt (fun z : ℂ => z-β) β := continuousAt_id.sub continuousAt_const
      simpa only [sub_self] using hc.tendsto
    filter_upwards [hn.eventually heq] with z hz
    simpa only [sub_add_cancel,F] using hz

/-- Actual analytic initial-value uniqueness at every complex ordinary point,
with the SAME original-coordinate operator. -/
theorem complexOriginalCenter_actual_germ_unique {r : ℕ}
    (t : Polynomial ℂ) (U : Matrix (Fin r) (Fin r) (Polynomial ℂ)) (β : ℂ)
    (hβ : t.eval β ≠ 0) (f g : Fin r → ℂ → ℂ)
    (hf : ClearedAnalyticSolutionGermAt t U β f)
    (hg : ClearedAnalyticSolutionGermAt t U β g)
    (h0 : ∀ i,f i β=g i β) :
    ∀ᶠ z in nhds β, ∀ i,f i z=g i z := by
  have hft := clearedAnalyticSolutionGermAt_translate t U β f hf
  have hgt := clearedAnalyticSolutionGermAt_translate t U β g hg
  have hfr := complexOrdinaryPoint_arbitrary_actual_germ_representation t U β hβ
    (fun i z => f i (z+β)) hft.1 hft.2
  have hgr := complexOrdinaryPoint_arbitrary_actual_germ_representation t U β hβ
    (fun i z => g i (z+β)) hgt.1 hgt.2
  have he : ∀ᶠ z in nhds (0:ℂ), ∀ i,f i (z+β)=g i (z+β) := by
    filter_upwards [hfr,hgr] with z hfz hgz
    intro i
    rw [hfz i,hgz i]
    simp only [zero_add,h0]
  have hn : Filter.Tendsto (fun z : ℂ => z-β) (nhds β) (nhds 0) := by
    have hc : ContinuousAt (fun z : ℂ => z-β) β := continuousAt_id.sub continuousAt_const
    simpa only [sub_self] using hc.tendsto
  simpa only [sub_add_cancel] using hn.eventually he

end StrictEUnit
end
