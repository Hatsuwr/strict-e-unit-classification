import ComplexOrdinaryAnalyticFrame
import V5ObservableRows

namespace StrictEUnit
open scoped Topology BigOperators Matrix
open Filter

private theorem v5_ordinary_shift_eval (p : Polynomial ℂ) (x z : ℂ) :
    (ordinaryPointPolynomialShift x p).eval (z - x) = p.eval z := by
  simp [ordinaryPointPolynomialShift_apply, Polynomial.eval_comp]

private theorem v5_polynomial_eval_analytic (p : Polynomial ℂ) (x : ℂ) :
    AnalyticAt ℂ (fun z => p.eval z) x := by
  simpa [Polynomial.aeval_def] using
    (analyticAt_id : AnalyticAt ℂ (fun z : ℂ => z) x).aeval_polynomial p

/-- Translate the existing convergent normalized frame back to the original point
and divide only by the common denominator, which is nonzero at that point. -/
theorem v5_ordinary_rational_system_columns {d : ℕ} (t : Polynomial ℂ)
    (P : Matrix (Fin d) (Fin d) (Polynomial ℂ)) (x : ℂ) (ht : t.eval x ≠ 0) :
    let A : Fin d → Fin d → ℂ → ℂ := fun k l z => (t.eval z)⁻¹ * (P k l).eval z
    (∀ k l, AnalyticAt ℂ (A k l) x) ∧
      ∃ U : Fin d → Fin d → ℂ → ℂ,
        (∀ j k, AnalyticAt ℂ (U j k) x) ∧
        (∀ j k, U j k x = if k = j then 1 else 0) ∧
        ∀ j k, ∀ᶠ z in 𝓝 x, deriv (U j k) z = ∑ l, A k l z * U j l z := by
  classical
  dsimp only
  refine ⟨fun k l => ((v5_polynomial_eval_analytic t x).fun_inv ht).mul
    (v5_polynomial_eval_analytic (P k l) x), ?_⟩
  obtain ⟨C, hC, hY, h0, hode⟩ := complexOrdinaryPoint_actual_frame_disk t P x ht
  let Y := complexOrdinaryAnalyticMatrix t P x
  let U : Fin d → Fin d → ℂ → ℂ := fun j k z => Y k j (z - x)
  have hR : (0 : ENNReal) < (ordinaryGermRadius C hC : ENNReal) := by
    exact_mod_cast ordinaryGermRadius_pos C hC
  have hball : ∀ᶠ w in 𝓝 (0 : ℂ),
      w ∈ EMetric.ball 0 (ordinaryGermRadius C hC : ENNReal) :=
    EMetric.ball_mem_nhds 0 hR
  have hshiftA : AnalyticAt ℂ (fun z : ℂ => z - x) x :=
    (analyticAt_id : AnalyticAt ℂ (fun z : ℂ => z) x).sub analyticAt_const
  have hshift : Tendsto (fun z : ℂ => z - x) (𝓝 x) (𝓝 0) := by
    simpa using hshiftA.continuousAt.tendsto
  refine ⟨U, ?_, ?_, ?_⟩
  · intro j k
    have hY0 : AnalyticAt ℂ (Y k j) (0 : ℂ) := hY k j 0 (EMetric.mem_ball_self hR)
    exact hY0.comp_of_eq' hshiftA (sub_self x)
  · intro j k
    simpa [U, Y] using h0 k j
  · intro j k
    have hden := t.continuousAt.eventually_ne ht
    filter_upwards [hshift.eventually hball, hden] with z hz ht_z
    have he := hode (z - x) hz k j
    simp only [v5_ordinary_shift_eval] at he
    change t.eval z * deriv (Y k j) (z - x) =
      ∑ l, (P k l).eval z * Y l j (z - x) at he
    change deriv (fun w => Y k j (w - x)) z =
      ∑ l, ((t.eval z)⁻¹ * (P k l).eval z) * Y l j (z - x)
    rw [deriv_comp_sub_const]
    calc
      _ = (t.eval z)⁻¹ * (t.eval z * deriv (Y k j) (z - x)) := by
        rw [← mul_assoc, inv_mul_cancel₀ ht_z, one_mul]
      _ = _ := by
        rw [he, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        rw [mul_assoc]

#print axioms v5_ordinary_rational_system_columns
end StrictEUnit
