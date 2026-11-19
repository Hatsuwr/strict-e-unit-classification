import ComplexUniformGermDisks
import Mathlib.Topology.UnitInterval

noncomputable section
open scoped Topology BigOperators Matrix unitInterval
namespace StrictEUnit

/-- A continuous complex path has a finite, eventually stationary mesh whose
whole segments lie in prescribed-radius disks at their left endpoints. -/
theorem continuous_complex_path_disk_mesh (γ : unitInterval → ℂ) (hγ : Continuous γ)
    (R : ℝ) (hR : 0 < R) :
    ∃ τ : ℕ → unitInterval,τ 0=0 ∧ Monotone τ ∧
      (∃ N,∀ n ≥ N,τ n=1) ∧ ∀ n q,q ∈ Set.Icc (τ n) (τ (n+1)) →
        dist (γ (τ n)) (γ q)<R := by
  let c : unitInterval → Set unitInterval := fun u => γ ⁻¹' Metric.ball (γ u) (R/2)
  have hopen (u : unitInterval) : IsOpen (c u) := Metric.isOpen_ball.preimage hγ
  have hcover : Set.univ ⊆ ⋃ u : unitInterval,c u := by
    intro u hu
    exact Set.mem_iUnion.mpr ⟨u,Metric.mem_ball_self (half_pos hR)⟩
  obtain ⟨τ,h0,hmono,hstop,hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval (c:=c) hopen hcover
  refine ⟨τ,h0,hmono,hstop,?_⟩
  intro n q hq
  obtain ⟨u,hu⟩ := hsub n
  have hl : dist (γ (τ n)) (γ u)<R/2 :=
    Metric.mem_ball.mp (hu ⟨le_rfl,hmono (Nat.le_succ n)⟩)
  have hr : dist (γ u) (γ q)<R/2 := Metric.mem_ball'.mp (hu hq)
  calc
    _ ≤ dist (γ (τ n)) (γ u)+dist (γ u) (γ q) := dist_triangle _ _ _
    _ < R/2+R/2 := add_lt_add hl hr
    _ = R := add_halves R

theorem clearedAnalyticSolutionOn_germ_at_mem {r : ℕ}
    (t : Polynomial ℂ) (U : Matrix (Fin r) (Fin r) (Polynomial ℂ))
    (s : Set ℂ) (hopen : IsOpen s) (F : Fin r → ℂ → ℂ)
    (hF : ClearedAnalyticSolutionOn t U s F) (β : ℂ) (hβ : β ∈ s) :
    ClearedAnalyticSolutionGermAt t U β F := by
  refine ⟨fun i => hF.1 i β hβ,?_⟩
  filter_upwards [hopen.mem_nhds hβ] with z hz
  exact hF.2 z hz

/-- Local disks are chained as germs. No equality on the union of all disks
or path-independent/single-valued continuation is asserted. -/
theorem cleared_analytic_continuation_along_small_steps {r : ℕ}
    (t : Polynomial ℂ) (U : Matrix (Fin r) (Fin r) (Polynomial ℂ))
    (b : ℕ → ℂ) (R : NNReal)
    (hstep : ∀ n,b (n+1) ∈ EMetric.ball (b n) (R:ENNReal))
    (hext : ∀ n,∀ f : Fin r → ℂ → ℂ,ClearedAnalyticSolutionGermAt t U (b n) f →
      ∃ F : Fin r → ℂ → ℂ,
        ClearedAnalyticSolutionOn t U (EMetric.ball (b n) (R:ENNReal)) F ∧
        ∀ᶠ z in nhds (b n),∀ i,f i z=F i z)
    (f : Fin r → ℂ → ℂ) (hf : ClearedAnalyticSolutionGermAt t U (b 0) f) :
    ∃ F : ℕ → Fin r → ℂ → ℂ,
      (∀ n,ClearedAnalyticSolutionOn t U (EMetric.ball (b n) (R:ENNReal)) (F n)) ∧
      (∀ᶠ z in nhds (b 0),∀ i,f i z=F 0 i z) ∧
      ∀ n,∀ᶠ z in nhds (b (n+1)),∀ i,F n i z=F (n+1) i z := by
  classical
  let S (n : ℕ) := {F : Fin r → ℂ → ℂ //
    ClearedAnalyticSolutionOn t U (EMetric.ball (b n) (R:ENNReal)) F}
  obtain ⟨F0,hF0,hstart⟩ := hext 0 f hf
  let base : S 0 := ⟨F0,hF0⟩
  have advance (n : ℕ) (F : S n) : ∃ G : S (n+1),
      ∀ᶠ z in nhds (b (n+1)),∀ i,F.val i z=G.val i z := by
    have hg := clearedAnalyticSolutionOn_germ_at_mem t U _ EMetric.isOpen_ball
      F.val F.property (b (n+1)) (hstep n)
    obtain ⟨G,hG,hmatch⟩ := hext (n+1) F.val hg
    exact ⟨⟨G,hG⟩,hmatch⟩
  let seq : (n : ℕ) → S n := fun n => Nat.rec (motive:=S) base
    (fun n F => Classical.choose (advance n F)) n
  refine ⟨fun n => (seq n).val,fun n => (seq n).property,?_,?_⟩
  · exact hstart
  · intro n
    change ∀ᶠ z in nhds (b (n+1)),∀ i,
      (seq n).val i z=(Classical.choose (advance n (seq n))).val i z
    exact Classical.choose_spec (advance n (seq n))

/-- Every actual analytic germ of the literal SAME polynomial system can be
continued along any continuous path in its regular locus, as a finite chain
of compatible disk germs. The path may have monodromy; no singular endpoint
or arithmetic normalization is assumed or concluded. -/
theorem complex_regular_path_actual_germ_continuation {r : ℕ}
    (t : Polynomial ℂ) (U : Matrix (Fin r) (Fin r) (Polynomial ℂ))
    (γ : unitInterval → ℂ) (hγ : Continuous γ)
    (hregular : ∀ q,t.eval (γ q) ≠ 0)
    (f : Fin r → ℂ → ℂ) (hf : ClearedAnalyticSolutionGermAt t U (γ 0) f) :
    ∃ R : NNReal,0<R ∧ ∃ τ : ℕ → unitInterval,
      τ 0=0 ∧ Monotone τ ∧ (∃ N,∀ n ≥ N,τ n=1) ∧
      (∀ n q,q ∈ Set.Icc (τ n) (τ (n+1)) → γ q ∈ EMetric.ball (γ (τ n)) (R:ENNReal)) ∧
      ∃ F : ℕ → Fin r → ℂ → ℂ,
        (∀ n,ClearedAnalyticSolutionOn t U (EMetric.ball (γ (τ n)) (R:ENNReal)) (F n)) ∧
        (∀ᶠ z in nhds (γ 0),∀ i,f i z=F 0 i z) ∧
        ∀ n,∀ᶠ z in nhds (γ (τ (n+1))),∀ i,F n i z=F (n+1) i z := by
  have hcompact : IsCompact (Set.range γ) := isCompact_range hγ
  have hs : ∀ β ∈ Set.range γ,t.eval β ≠ 0 := by
    rintro β ⟨q,rfl⟩
    exact hregular q
  obtain ⟨M,hM,hext⟩ := complexOriginalCenter_uniform_germ_disks_on_compact
    t U (Set.range γ) hcompact hs
  let R := ordinaryGermRadius M hM
  have hR : 0<R := ordinaryGermRadius_pos M hM
  have hRreal : (0:ℝ)<R := hR
  obtain ⟨τ,h0,hmono,hstop,hmesh⟩ := continuous_complex_path_disk_mesh γ hγ R hRreal
  have hseg (n : ℕ) (q : unitInterval) (hq : q ∈ Set.Icc (τ n) (τ (n+1))) :
      γ q ∈ EMetric.ball (γ (τ n)) (R:ENNReal) := by
    rw [EMetric.mem_ball,edist_lt_coe]
    change dist (γ q) (γ (τ n)) < (R:ℝ)
    simpa only [dist_comm] using hmesh n q hq
  have hstep (n : ℕ) : γ (τ (n+1)) ∈ EMetric.ball (γ (τ n)) (R:ENNReal) :=
    hseg n _ ⟨hmono (Nat.le_succ n),le_rfl⟩
  obtain ⟨F,hF,hstart,hmatch⟩ := cleared_analytic_continuation_along_small_steps t U
    (fun n => γ (τ n)) R hstep
    (fun n => hext (γ (τ n)) (Set.mem_range_self (τ n))) f (by simpa only [h0] using hf)
  exact ⟨R,hR,τ,h0,hmono,hstop,hseg,F,hF,by simpa only [h0] using hstart,hmatch⟩

end StrictEUnit
end
