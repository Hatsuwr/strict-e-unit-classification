import ComplexPolynomialSystemGrowth
import OrdinaryGermDiskExtension

noncomputable section
open scoped Topology BigOperators Matrix
namespace StrictEUnit

/-- The same normalized formal frame summed at an arbitrary complex center.
No arithmetic structure on the center or initial values is required. -/
def complexOrdinaryAnalyticMatrix {r : ℕ} (t : Polynomial ℂ)
    (U : Matrix (Fin r) (Fin r) (Polynomial ℂ)) (β : ℂ) :
    Matrix (Fin r) (Fin r) (ℂ → ℂ) :=
  fun i j => ordinaryGermSum (fun n => PowerSeries.coeff ℂ n
    (formalFundamentalMatrix (ordinaryPointClearedMatrix t U β) i j))

theorem complexOrdinaryPoint_fundamental_analytic_germs {r : ℕ}
    (t : Polynomial ℂ) (U : Matrix (Fin r) (Fin r) (Polynomial ℂ)) (β : ℂ)
    (hβ : t.eval β ≠ 0) :
    ∃ C : ℝ, ∃ hC : 1 ≤ C, ∀ i j,
      HasFPowerSeriesOnBall (complexOrdinaryAnalyticMatrix t U β i j)
        (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n
          (formalFundamentalMatrix (ordinaryPointClearedMatrix t U β) i j)))
        0 (ordinaryGermRadius C hC : ENNReal) := by
  obtain ⟨C,hC,hbound⟩ := complexOrdinaryPoint_fundamental_norm_bound t U β hβ
  exact ⟨C,hC,fun i j => ordinaryGerm_hasFPowerSeriesOnBall _ C hC
    (fun n => hbound n i j)⟩

/-- Actual existence for the literal SAME cleared system at EVERY complex
ordinary center, with an internally derived common disk and normalization. -/
theorem complexOrdinaryPoint_actual_frame_disk {r : ℕ}
    (t : Polynomial ℂ) (U : Matrix (Fin r) (Fin r) (Polynomial ℂ)) (β : ℂ)
    (hβ : t.eval β ≠ 0) :
    let Y := complexOrdinaryAnalyticMatrix t U β
    ∃ C : ℝ, ∃ hC : 1 ≤ C,
      (∀ i j,AnalyticOnNhd ℂ (Y i j)
        (EMetric.ball 0 (ordinaryGermRadius C hC : ENNReal))) ∧
      (∀ i j,Y i j 0=if i=j then 1 else 0) ∧
      ∀ z ∈ EMetric.ball 0 (ordinaryGermRadius C hC : ENNReal), ∀ i j,
        (ordinaryPointPolynomialShift β t).eval z*deriv (Y i j) z=
          ∑ l,(ordinaryPointPolynomialShift β (U i l)).eval z*Y l j z := by
  classical
  let Z := formalFundamentalMatrix (ordinaryPointClearedMatrix t U β)
  let Y := complexOrdinaryAnalyticMatrix t U β
  obtain ⟨C,hC,hOn⟩ := complexOrdinaryPoint_fundamental_analytic_germs t U β hβ
  have hAt i j : HasFPowerSeriesAt (Y i j)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n (Z i j))) 0 :=
    (hOn i j).hasFPowerSeriesAt
  have hform := ordinaryPointClearedMatrix_fundamental_cleared t U β hβ
  have hloc := ordinary_series_matrix_ode_eventually
    (ordinaryPointPolynomialShift β t)
    (fun i l => ordinaryPointPolynomialShift β (U i l)) Z Y hAt hform
  have hR : (0:ENNReal)<(ordinaryGermRadius C hC : ENNReal) := by
    exact_mod_cast ordinaryGermRadius_pos C hC
  have ha i j := (hOn i j).analyticOnNhd
  refine ⟨C,hC,ha,?_,?_⟩
  · intro i j
    have h0 := (hOn i j).coeff_zero (fun _ => (1:ℂ))
    have hz := congrArg (fun M : Matrix (Fin r) (Fin r) ℂ => M i j)
      (formalFundamentalMatrix_constantCoeff (ordinaryPointClearedMatrix t U β))
    change PowerSeries.constantCoeff ℂ (Z i j)=(1:Matrix (Fin r) (Fin r) ℂ) i j at hz
    have he : Y i j 0=PowerSeries.coeff ℂ 0 (Z i j) := by
      simpa only [FormalMultilinearSeries.ofScalars_apply_eq,pow_zero,smul_eq_mul,mul_one]
        using h0.symm
    change Y i j 0=_
    rw [he,PowerSeries.coeff_zero_eq_constantCoeff,hz,Matrix.one_apply]
  · exact analytic_matrix_cleared_ode_on_preconnected
      (EMetric.ball 0 (ordinaryGermRadius C hC : ENNReal))
      (Metric.isConnected_eball hR).isPreconnected (EMetric.mem_ball_self hR)
      (ordinaryPointPolynomialShift β t)
      (fun i l => ordinaryPointPolynomialShift β (U i l)) Y ha hloc

/-- Arbitrary complex initial vectors have actual solutions on one common
positive disk derived solely from the SAME polynomial system. -/
theorem complexOrdinaryPoint_all_initial_values_on_disk
    {r : ℕ}
    (t : Polynomial ℂ) (U : Matrix (Fin r) (Fin r) (Polynomial ℂ)) (α : ℂ)
    (hα : t.eval α ≠ 0) :
    ∃ C : ℝ, ∃ hC : 1 ≤ C, ∀ c : Fin r → ℂ,
      let F : Fin r → ℂ → ℂ := fun i z =>
        ∑ j,complexOrdinaryAnalyticMatrix t U α i j z*c j
      (∀ i,AnalyticOnNhd ℂ (F i)
        (EMetric.ball 0 (ordinaryGermRadius C hC : ENNReal))) ∧
      (∀ i,F i 0=c i) ∧
      ∀ z ∈ EMetric.ball 0 (ordinaryGermRadius C hC : ENNReal), ∀ i,
        (ordinaryPointPolynomialShift α t).eval z*deriv (F i) z=
          ∑ l,(ordinaryPointPolynomialShift α (U i l)).eval z*F l z := by
  classical
  obtain ⟨C,hC,hY,h0,hode⟩ := complexOrdinaryPoint_actual_frame_disk t U α hα
  refine ⟨C,hC,?_⟩
  intro c
  dsimp only
  have ha i : AnalyticOnNhd ℂ
      (fun z => ∑ j,complexOrdinaryAnalyticMatrix t U α i j z*c j)
      (EMetric.ball 0 (ordinaryGermRadius C hC : ENNReal)) :=
    Finset.univ.analyticOnNhd_sum (fun j _ => (hY i j).mul analyticOnNhd_const)
  refine ⟨ha,?_,?_⟩
  · intro i
    simp only [h0]
    simp
  · intro z hz i
    rw [deriv_sum (u:=Finset.univ)
      (A:=fun j z => complexOrdinaryAnalyticMatrix t U α i j z*c j)
      (fun j hj => ((hY i j z hz).mul analyticAt_const).differentiableAt)]
    simp only [deriv_mul_const_field,Finset.mul_sum,Finset.sum_mul]
    calc
      _ = ∑ j,∑ l,((ordinaryPointPolynomialShift α (U i l)).eval z*
            complexOrdinaryAnalyticMatrix t U α l j z)*c j := by
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

end StrictEUnit
end
