import ArbitraryOrdinaryAnalyticGerms
import Mathlib.Analysis.Analytic.Uniqueness

noncomputable section
open scoped Topology BigOperators Matrix
namespace StrictEUnit

theorem analyticAt_has_ordinary_series (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) :
    ∃ P : PowerSeries ℂ, HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n P)) 0 := by
  obtain ⟨p,hp⟩ := hf
  let P : PowerSeries ℂ := PowerSeries.mk (fun n => p.coeff n)
  refine ⟨P,?_⟩
  have he : p=FormalMultilinearSeries.ofScalars ℂ
      (fun n => PowerSeries.coeff ℂ n P) := by
    ext n u
    simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
      FormalMultilinearSeries.coeff_ofScalars,P,PowerSeries.coeff_mk]
  rw [← he]
  exact hp

theorem ordinary_series_eq_of_eventually
    (f g : ℂ → ℂ) (P Q : PowerSeries ℂ)
    (hf : HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n P)) 0)
    (hg : HasFPowerSeriesAt g
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n Q)) 0)
    (heq : ∀ᶠ z in nhds (0:ℂ),f z=g z) : P=Q := by
  have h := hf.eq_formalMultilinearSeries_of_eventually hg heq
  apply PowerSeries.ext
  intro n
  simpa only [FormalMultilinearSeries.coeff_ofScalars] using
    congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) h

/-- The converse transfer takes only actual analytic germs and an actual local
ODE; formal coefficients and their exact differential equation are derived. -/
theorem ordinary_actual_vector_ode_formal {r : ℕ}
    (t : Polynomial ℂ) (U : Matrix (Fin r) (Fin r) (Polynomial ℂ))
    (v : Fin r → PowerSeries ℂ) (f : Fin r → ℂ → ℂ)
    (hf : ∀ i,HasFPowerSeriesAt (f i)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n (v i))) 0)
    (hode : ∀ᶠ z in nhds (0:ℂ), ∀ i,
      t.eval z*deriv (f i) z=∑ l,(U i l).eval z*f l z) :
    ∀ i,(t:PowerSeries ℂ)*PowerSeries.derivative ℂ (v i)=
      ∑ l,(U i l:PowerSeries ℂ)*v l := by
  intro i
  have hl := hasFPowerSeriesAt_mul_ofScalars (fun z => t.eval z) (deriv (f i)) _ _
    (hasFPowerSeriesAt_polynomial_ofScalars t)
    (hasFPowerSeriesAt_deriv_ofScalars (f i) (v i) (hf i))
  have hr := hasFPowerSeriesAt_finset_sum_ofScalars Finset.univ
    (fun l z => (U i l).eval z*f l z) (fun l => (U i l:PowerSeries ℂ)*v l)
    (fun l hl => hasFPowerSeriesAt_mul_ofScalars _ _ _ _
      (hasFPowerSeriesAt_polynomial_ofScalars (U i l)) (hf l))
  exact ordinary_series_eq_of_eventually _ _ _ _ hl hr
    (hode.mono (fun z hz => hz i))

theorem ordinaryPoint_mapped_denominator_clear
    {K : Type*} [Field K] {r : ℕ}
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K)) (α : K)
    (hα : t.eval α ≠ 0) (σ : K →+* ℂ) (i l : Fin r) :
    ((ordinaryPointPolynomialShift α t).map σ:PowerSeries ℂ)*
        PowerSeries.map σ (ordinaryPointClearedMatrix t U α i l)=
      ((ordinaryPointPolynomialShift α (U i l)).map σ:PowerSeries ℂ) := by
  have hc : PowerSeries.constantCoeff K (ordinaryPointPolynomialSeries α t) ≠ 0 := by
    rw [ordinaryPointPolynomialSeries_constantCoeff]
    exact hα
  have hk : ordinaryPointPolynomialSeries α t*ordinaryPointClearedMatrix t U α i l=
      ordinaryPointPolynomialSeries α (U i l) := by
    change ordinaryPointPolynomialSeries α t*
      (ordinaryPointPolynomialSeries α (U i l)*(ordinaryPointPolynomialSeries α t)⁻¹)=_
    calc
      _ = (ordinaryPointPolynomialSeries α t*(ordinaryPointPolynomialSeries α t)⁻¹)*
          ordinaryPointPolynomialSeries α (U i l) := by ring
      _ = _ := by rw [PowerSeries.mul_inv_cancel _ hc,one_mul]
  have hm := congrArg (PowerSeries.map σ) hk
  simpa only [map_mul,ordinaryPointPolynomialSeries,← Polynomial.polynomial_map_coe] using hm

/-- Every actual analytic solution germ is the SAME normalized frame times
its actual initial vector. No formal representation, growth, arithmetic or
rational-input hypothesis is supplied for the arbitrary actual germ. -/
theorem ordinaryPoint_arbitrary_actual_germ_representation
    {K : Type*} [Field K] [NumberField K] {r : ℕ}
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K)) (α : K)
    (hα : t.eval α ≠ 0) (σ : K →+* ℂ)
    (f : Fin r → ℂ → ℂ) (hf : ∀ i,AnalyticAt ℂ (f i) 0)
    (hode : ∀ᶠ z in nhds (0:ℂ), ∀ i,
      (ordinaryPointPolynomialShift α t).eval₂ σ z*deriv (f i) z=
        ∑ l,(ordinaryPointPolynomialShift α (U i l)).eval₂ σ z*f l z) :
    ∀ᶠ z in nhds (0:ℂ), ∀ i,
      f i z=∑ j,ordinaryPointAnalyticMatrix σ t U α i j z*f j 0 := by
  classical
  choose v hv using fun i => analyticAt_has_ordinary_series (f i) (hf i)
  let B := (ordinaryPointClearedMatrix t U α).map (PowerSeries.map σ)
  let Z := (formalFundamentalMatrix (ordinaryPointClearedMatrix t U α)).map (PowerSeries.map σ)
  let s : Polynomial ℂ := (ordinaryPointPolynomialShift α t).map σ
  let V : Matrix (Fin r) (Fin r) (Polynomial ℂ) :=
    fun i l => (ordinaryPointPolynomialShift α (U i l)).map σ
  have hform : ∀ i,(s:PowerSeries ℂ)*PowerSeries.derivative ℂ (v i)=
      ∑ l,(V i l:PowerSeries ℂ)*v l := by
    apply ordinary_actual_vector_ode_formal s V v f hv
    simpa only [s,V,Polynomial.eval_map] using hode
  have hs : (s:PowerSeries ℂ) ≠ 0 := by
    intro hz
    have h0 := congrArg (PowerSeries.constantCoeff ℂ) hz
    have he : PowerSeries.constantCoeff ℂ (s:PowerSeries ℂ)=σ (t.eval α) := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,Polynomial.coeff_coe]
      dsimp only [s]
      rw [Polynomial.coeff_map]
      congr 1
      exact ordinaryPointPolynomialSeries_constantCoeff α t
    rw [he,map_zero] at h0
    exact hα (σ.injective (by simpa using h0))
  have hdiff : ∀ i,PowerSeries.derivative ℂ (v i)=∑ l,B i l*v l := by
    intro i
    apply mul_left_cancel₀ hs
    rw [hform i,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    rw [← mul_assoc]
    change (V i l:PowerSeries ℂ)*v l =
      (((ordinaryPointPolynomialShift α t).map σ:PowerSeries ℂ)*
        PowerSeries.map σ (ordinaryPointClearedMatrix t U α i l))*v l
    rw [ordinaryPoint_mapped_denominator_clear t U α hα σ]
  obtain ⟨hZ,hZ0⟩ := ordinaryPoint_mapped_formal_frame t U α σ
  have hrep := powerSeries_solution_eq_frame_initial B Z hZ hZ0 v hdiff
  obtain ⟨C,hC,hOn⟩ := ordinaryPoint_fundamental_analytic_germs t U α hα σ
  have hc (j : Fin r) : PowerSeries.constantCoeff ℂ (v j)=f j 0 := by
    have h0 := (hv j).coeff_zero (fun _ => (1:ℂ))
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq,
      PowerSeries.coeff_zero_eq_constantCoeff,pow_zero,smul_eq_mul,mul_one] using h0
  apply Filter.eventually_all.2
  intro i
  have hsum := hasFPowerSeriesAt_finset_sum_ofScalars Finset.univ
    (fun j z => ordinaryPointAnalyticMatrix σ t U α i j z*f j 0)
    (fun j => Z i j*PowerSeries.C ℂ (f j 0)) (fun j hj =>
      hasFPowerSeriesAt_mul_ofScalars _ _ _ _
        (by simpa only [Z,Matrix.map_apply,PowerSeries.coeff_map] using
          (hOn i j).hasFPowerSeriesAt)
        (by simpa only [Polynomial.eval_C,Polynomial.coe_C] using
          hasFPowerSeriesAt_polynomial_ofScalars (Polynomial.C (f j 0))))
  have hi := hv i
  rw [hrep i] at hi
  simp_rw [hc] at hi
  exact eventually_eq_of_same_ordinary_series _ _ _ hi hsum

end StrictEUnit
end
