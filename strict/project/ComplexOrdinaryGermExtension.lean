import ComplexOrdinaryAnalyticFrame

noncomputable section
open scoped Topology BigOperators Matrix
namespace StrictEUnit

/-- Local uniqueness and spanning for arbitrary actual analytic germs, now at
any complex ordinary center of the literal supplied polynomial system. -/
theorem complexOrdinaryPoint_arbitrary_actual_germ_representation {r : ℕ}
    (t : Polynomial ℂ) (U : Matrix (Fin r) (Fin r) (Polynomial ℂ)) (α : ℂ)
    (hα : t.eval α ≠ 0)
    (f : Fin r → ℂ → ℂ) (hf : ∀ i,AnalyticAt ℂ (f i) 0)
    (hode : ∀ᶠ z in nhds (0:ℂ), ∀ i,
      (ordinaryPointPolynomialShift α t).eval z*deriv (f i) z=
        ∑ l,(ordinaryPointPolynomialShift α (U i l)).eval z*f l z) :
    ∀ᶠ z in nhds (0:ℂ), ∀ i,
      f i z=∑ j,complexOrdinaryAnalyticMatrix t U α i j z*f j 0 := by
  classical
  choose v hv using fun i => analyticAt_has_ordinary_series (f i) (hf i)
  let B := ordinaryPointClearedMatrix t U α
  let Z := formalFundamentalMatrix B
  let s := ordinaryPointPolynomialShift α t
  let V : Matrix (Fin r) (Fin r) (Polynomial ℂ) :=
    fun i l => ordinaryPointPolynomialShift α (U i l)
  have hform := ordinary_actual_vector_ode_formal s V v f hv hode
  have hs : (s:PowerSeries ℂ) ≠ 0 := by
    intro hz
    have h0 := congrArg (PowerSeries.constantCoeff ℂ) hz
    have he : PowerSeries.constantCoeff ℂ (s:PowerSeries ℂ)=t.eval α :=
      ordinaryPointPolynomialSeries_constantCoeff α t
    rw [he,map_zero] at h0
    exact hα h0
  have hclear (i l : Fin r) : (s:PowerSeries ℂ)*B i l=(V i l:PowerSeries ℂ) := by
    have h := ordinaryPoint_mapped_denominator_clear t U α hα (RingHom.id ℂ) i l
    simpa only [Polynomial.map_id,PowerSeries.map_id] using h
  have hdiff : ∀ i,PowerSeries.derivative ℂ (v i)=∑ l,B i l*v l := by
    intro i
    apply mul_left_cancel₀ hs
    rw [hform i,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    rw [← mul_assoc,hclear]
  have hrep := powerSeries_solution_eq_frame_initial B Z
    (formalFundamentalMatrix_derivative B) (formalFundamentalMatrix_constantCoeff B) v hdiff
  obtain ⟨C,hC,hOn⟩ := complexOrdinaryPoint_fundamental_analytic_germs t U α hα
  have hc (j : Fin r) : PowerSeries.constantCoeff ℂ (v j)=f j 0 := by
    have h0 := (hv j).coeff_zero (fun _ => (1:ℂ))
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq,
      PowerSeries.coeff_zero_eq_constantCoeff,pow_zero,smul_eq_mul,mul_one] using h0
  apply Filter.eventually_all.2
  intro i
  have hsum := hasFPowerSeriesAt_finset_sum_ofScalars Finset.univ
    (fun j z => complexOrdinaryAnalyticMatrix t U α i j z*f j 0)
    (fun j => Z i j*PowerSeries.C ℂ (f j 0)) (fun j hj =>
      hasFPowerSeriesAt_mul_ofScalars _ _ _ _ (hOn i j).hasFPowerSeriesAt
        (by simpa only [Polynomial.eval_C,Polynomial.coe_C] using
          hasFPowerSeriesAt_polynomial_ofScalars (Polynomial.C (f j 0))))
  have hi := hv i
  rw [hrep i] at hi
  simp_rw [hc] at hi
  exact eventually_eq_of_same_ordinary_series _ _ _ hi hsum

/-- The extension radius depends only on the fixed system and the arbitrary
complex ordinary center, before quantification over arbitrary solution germs. -/
theorem complexOrdinaryPoint_arbitrary_actual_germ_disk_extension {r : ℕ}
    (t : Polynomial ℂ) (U : Matrix (Fin r) (Fin r) (Polynomial ℂ)) (α : ℂ)
    (hα : t.eval α ≠ 0) :
    ∃ C : ℝ, ∃ hC : 1 ≤ C, ∀ f : Fin r → ℂ → ℂ,
      (∀ i,AnalyticAt ℂ (f i) 0) →
      (∀ᶠ z in nhds (0:ℂ), ∀ i,
        (ordinaryPointPolynomialShift α t).eval z*deriv (f i) z=
          ∑ l,(ordinaryPointPolynomialShift α (U i l)).eval z*f l z) →
      ∃ F : Fin r → ℂ → ℂ,
        (∀ i,AnalyticOnNhd ℂ (F i)
          (EMetric.ball 0 (ordinaryGermRadius C hC : ENNReal))) ∧
        (∀ᶠ z in nhds (0:ℂ), ∀ i,f i z=F i z) ∧
        ∀ z ∈ EMetric.ball 0 (ordinaryGermRadius C hC : ENNReal), ∀ i,
          (ordinaryPointPolynomialShift α t).eval z*deriv (F i) z=
            ∑ l,(ordinaryPointPolynomialShift α (U i l)).eval z*F l z := by
  obtain ⟨C,hC,hall⟩ := complexOrdinaryPoint_all_initial_values_on_disk t U α hα
  refine ⟨C,hC,?_⟩
  intro f hf hode
  obtain ⟨hF,h0,hFode⟩ := hall (fun j => f j 0)
  exact ⟨_,hF,complexOrdinaryPoint_arbitrary_actual_germ_representation t U α hα f hf hode,hFode⟩

end StrictEUnit
end
