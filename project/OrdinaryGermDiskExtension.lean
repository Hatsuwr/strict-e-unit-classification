import ArbitraryActualOrdinaryGerms
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.NormedSpace.Connected

noncomputable section
open scoped Topology BigOperators Matrix
namespace StrictEUnit

/-- Analytic identity extends the actual cleared equation over the whole
connected analytic domain, without dividing by the clearing polynomial. -/
theorem analytic_matrix_cleared_ode_on_preconnected
    {r : ℕ} (s : Set ℂ) (hs : IsPreconnected s) (h0 : (0:ℂ) ∈ s)
    (t : Polynomial ℂ) (U : Matrix (Fin r) (Fin r) (Polynomial ℂ))
    (Y : Matrix (Fin r) (Fin r) (ℂ → ℂ))
    (hY : ∀ i j,AnalyticOnNhd ℂ (Y i j) s)
    (hlocal : ∀ᶠ z in nhds (0:ℂ), ∀ i j,
      t.eval z*deriv (Y i j) z=∑ l,(U i l).eval z*Y l j z) :
    ∀ z ∈ s, ∀ i j,t.eval z*deriv (Y i j) z=∑ l,(U i l).eval z*Y l j z := by
  intro z hz i j
  have hp (P : Polynomial ℂ) : AnalyticOnNhd ℂ (fun z => P.eval z) s :=
    (AnalyticOnNhd.eval_polynomial (𝕜:=ℂ) P).mono (Set.subset_univ s)
  have hl : AnalyticOnNhd ℂ (fun z => t.eval z*deriv (Y i j) z) s :=
    (hp t).mul (hY i j).deriv
  have hr : AnalyticOnNhd ℂ (fun z => ∑ l,(U i l).eval z*Y l j z) s :=
    Finset.univ.analyticOnNhd_sum (fun l _ => (hp (U i l)).mul (hY l j))
  exact (hl.eqOn_of_preconnected_of_eventuallyEq hr hs h0
    (hlocal.mono (fun z hz => hz i j))) hz

/-- The SAME analytic fundamental frame satisfies the actual cleared system
on its full internally proved positive disk, not only as a germ. -/
theorem ordinaryPoint_actual_frame_disk
    {K : Type*} [Field K] [NumberField K] {r : ℕ}
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K)) (α : K)
    (hα : t.eval α ≠ 0) (σ : K →+* ℂ) :
    let Y := ordinaryPointAnalyticMatrix σ t U α
    ∃ C : ℝ, ∃ hC : 1 ≤ C,
      (∀ i j,AnalyticOnNhd ℂ (Y i j)
        (EMetric.ball 0 (ordinaryGermRadius C hC : ENNReal))) ∧
      (∀ i j,Y i j 0=if i=j then 1 else 0) ∧
      ∀ z ∈ EMetric.ball 0 (ordinaryGermRadius C hC : ENNReal), ∀ i j,
        (ordinaryPointPolynomialShift α t).eval₂ σ z*deriv (Y i j) z=
          ∑ l,(ordinaryPointPolynomialShift α (U i l)).eval₂ σ z*Y l j z := by
  obtain ⟨C,hC,hOn,h0,hode⟩ := ordinaryPoint_actual_cleared_system t U α hα σ
  have hR : (0:ENNReal)<(ordinaryGermRadius C hC : ENNReal) := by
    exact_mod_cast ordinaryGermRadius_pos C hC
  have hY i j := (hOn i j).analyticOnNhd
  refine ⟨C,hC,hY,h0,?_⟩
  have he := analytic_matrix_cleared_ode_on_preconnected
    (EMetric.ball 0 (ordinaryGermRadius C hC : ENNReal))
    (Metric.isConnected_eball hR).isPreconnected (EMetric.mem_ball_self hR)
    ((ordinaryPointPolynomialShift α t).map σ)
    (fun i l => (ordinaryPointPolynomialShift α (U i l)).map σ)
    (ordinaryPointAnalyticMatrix σ t U α) hY
    (by simpa only [Polynomial.eval_map] using hode)
  simpa only [Polynomial.eval_map] using he

/-- Arbitrary complex initial vectors have actual solutions on one common
positive disk derived solely from the SAME polynomial system. -/
theorem ordinaryPoint_all_initial_values_on_disk
    {K : Type*} [Field K] [NumberField K] {r : ℕ}
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K)) (α : K)
    (hα : t.eval α ≠ 0) (σ : K →+* ℂ) :
    ∃ C : ℝ, ∃ hC : 1 ≤ C, ∀ c : Fin r → ℂ,
      let F : Fin r → ℂ → ℂ := fun i z =>
        ∑ j,ordinaryPointAnalyticMatrix σ t U α i j z*c j
      (∀ i,AnalyticOnNhd ℂ (F i)
        (EMetric.ball 0 (ordinaryGermRadius C hC : ENNReal))) ∧
      (∀ i,F i 0=c i) ∧
      ∀ z ∈ EMetric.ball 0 (ordinaryGermRadius C hC : ENNReal), ∀ i,
        (ordinaryPointPolynomialShift α t).eval₂ σ z*deriv (F i) z=
          ∑ l,(ordinaryPointPolynomialShift α (U i l)).eval₂ σ z*F l z := by
  classical
  obtain ⟨C,hC,hY,h0,hode⟩ := ordinaryPoint_actual_frame_disk t U α hα σ
  refine ⟨C,hC,?_⟩
  intro c
  dsimp only
  have ha i : AnalyticOnNhd ℂ
      (fun z => ∑ j,ordinaryPointAnalyticMatrix σ t U α i j z*c j)
      (EMetric.ball 0 (ordinaryGermRadius C hC : ENNReal)) :=
    Finset.univ.analyticOnNhd_sum (fun j _ => (hY i j).mul analyticOnNhd_const)
  refine ⟨ha,?_,?_⟩
  · intro i
    simp only [h0]
    simp
  · intro z hz i
    rw [deriv_sum (u:=Finset.univ)
      (A:=fun j z => ordinaryPointAnalyticMatrix σ t U α i j z*c j)
      (fun j hj => ((hY i j z hz).mul analyticAt_const).differentiableAt)]
    simp only [deriv_mul_const_field,Finset.mul_sum,Finset.sum_mul]
    calc
      _ = ∑ j,∑ l,((ordinaryPointPolynomialShift α (U i l)).eval₂ σ z*
            ordinaryPointAnalyticMatrix σ t U α l j z)*c j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [← mul_assoc,hode z hz i j,Finset.sum_mul]
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro l hl
        apply Finset.sum_congr rfl
        intro j hj
        ring

/-- Every actual analytic solution germ extends to the same positive disk.
This is local disk extension; path continuation toward a singular center is
not asserted here. Initial values may be arbitrary complex numbers. -/
theorem ordinaryPoint_arbitrary_actual_germ_disk_extension
    {K : Type*} [Field K] [NumberField K] {r : ℕ}
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K)) (α : K)
    (hα : t.eval α ≠ 0) (σ : K →+* ℂ) :
    ∃ C : ℝ, ∃ hC : 1 ≤ C, ∀ f : Fin r → ℂ → ℂ,
      (∀ i,AnalyticAt ℂ (f i) 0) →
      (∀ᶠ z in nhds (0:ℂ), ∀ i,
        (ordinaryPointPolynomialShift α t).eval₂ σ z*deriv (f i) z=
          ∑ l,(ordinaryPointPolynomialShift α (U i l)).eval₂ σ z*f l z) →
      ∃ F : Fin r → ℂ → ℂ,
        (∀ i,AnalyticOnNhd ℂ (F i)
          (EMetric.ball 0 (ordinaryGermRadius C hC : ENNReal))) ∧
        (∀ᶠ z in nhds (0:ℂ), ∀ i,f i z=F i z) ∧
        ∀ z ∈ EMetric.ball 0 (ordinaryGermRadius C hC : ENNReal), ∀ i,
          (ordinaryPointPolynomialShift α t).eval₂ σ z*deriv (F i) z=
            ∑ l,(ordinaryPointPolynomialShift α (U i l)).eval₂ σ z*F l z := by
  obtain ⟨C,hC,hall⟩ := ordinaryPoint_all_initial_values_on_disk t U α hα σ
  refine ⟨C,hC,?_⟩
  intro f hf hode
  obtain ⟨hF,h0,hFode⟩ := hall (fun j => f j 0)
  exact ⟨_,hF,ordinaryPoint_arbitrary_actual_germ_representation t U α hα σ f hf hode,hFode⟩

end StrictEUnit
end
