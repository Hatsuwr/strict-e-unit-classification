import FormalOrdinarySolutionUniqueness

noncomputable section
open scoped Topology BigOperators Matrix
namespace StrictEUnit

/-- The mapped SAME formal frame retains its actual equation and initial value. -/
theorem ordinaryPoint_mapped_formal_frame
    {K : Type*} [Field K] [NumberField K] {r : ℕ}
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K)) (α : K)
    (σ : K →+* ℂ) :
    let B := (ordinaryPointClearedMatrix t U α).map (PowerSeries.map σ)
    let Z := (formalFundamentalMatrix (ordinaryPointClearedMatrix t U α)).map (PowerSeries.map σ)
    Z.map (PowerSeries.derivative ℂ)=B*Z ∧ Z.map (PowerSeries.constantCoeff ℂ)=1 := by
  let BK := ordinaryPointClearedMatrix t U α
  let ZK := formalFundamentalMatrix BK
  let ψ : PowerSeries K →+* PowerSeries ℂ := PowerSeries.map σ
  constructor
  · apply Matrix.ext
    intro i j
    have h := congrArg (fun M : Matrix (Fin r) (Fin r) (PowerSeries K) => M i j)
      (formalFundamentalMatrix_derivative BK)
    change PowerSeries.derivative K (ZK i j)=(BK*ZK) i j at h
    change PowerSeries.derivative ℂ (ψ (ZK i j))=(BK.map ψ*ZK.map ψ) i j
    calc
      _ = ψ (PowerSeries.derivative K (ZK i j)) := (ordinaryBorel_map_derivative σ (ZK i j)).symm
      _ = ψ ((BK*ZK) i j) := congrArg ψ h
      _ = _ := RingHom.map_matrix_mul BK ZK i j ψ
  · apply Matrix.ext
    intro i j
    change PowerSeries.constantCoeff ℂ (ψ (ZK i j))=(1:Matrix (Fin r) (Fin r) ℂ) i j
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    have h := congrArg (fun M : Matrix (Fin r) (Fin r) K => M i j)
      (formalFundamentalMatrix_constantCoeff BK)
    change PowerSeries.constantCoeff K (ZK i j)=(1:Matrix (Fin r) (Fin r) K) i j at h
    rw [h,Matrix.one_apply,Matrix.one_apply]
    split_ifs <;> simp

theorem ordinary_series_vector_ode_eventually {r : ℕ}
    (t : Polynomial ℂ) (U : Matrix (Fin r) (Fin r) (Polynomial ℂ))
    (v : Fin r → PowerSeries ℂ) (F : Fin r → ℂ → ℂ)
    (hF : ∀ i, HasFPowerSeriesAt (F i)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n (v i))) 0)
    (hode : ∀ i,(t:PowerSeries ℂ)*PowerSeries.derivative ℂ (v i)=
      ∑ l,(U i l:PowerSeries ℂ)*v l) :
    ∀ᶠ z in nhds (0:ℂ), ∀ i,
      t.eval z*deriv (F i) z=∑ l,(U i l).eval z*F l z := by
  apply Filter.eventually_all.2
  intro i
  have hl := hasFPowerSeriesAt_mul_ofScalars (fun z => t.eval z) (deriv (F i)) _ _
    (hasFPowerSeriesAt_polynomial_ofScalars t)
    (hasFPowerSeriesAt_deriv_ofScalars (F i) (v i) (hF i))
  have hr := hasFPowerSeriesAt_finset_sum_ofScalars Finset.univ
    (fun l z => (U i l).eval z*F l z) (fun l => (U i l:PowerSeries ℂ)*v l)
    (fun l hl => hasFPowerSeriesAt_mul_ofScalars _ _ _ _
      (hasFPowerSeriesAt_polynomial_ofScalars (U i l)) (hF l))
  rw [hode i] at hl
  exact eventually_eq_of_same_ordinary_series _ _ _ hl hr

/-- EVERY formal complex solution germ of the SAME ordinary system is realized
by actual analytic functions. No coefficient growth, arithmetic, convergence or
representation hypothesis is imposed on this arbitrary germ. -/
theorem ordinaryPoint_arbitrary_formal_germ_realization
    {K : Type*} [Field K] [NumberField K] {r : ℕ}
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K)) (α : K)
    (hα : t.eval α ≠ 0) (σ : K →+* ℂ)
    (v : Fin r → PowerSeries ℂ)
    (hv : ∀ i,PowerSeries.derivative ℂ (v i)=
      ∑ l,PowerSeries.map σ (ordinaryPointClearedMatrix t U α i l)*v l) :
    ∃ F : Fin r → ℂ → ℂ,
      (∀ i,HasFPowerSeriesAt (F i)
        (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n (v i))) 0) ∧
      (∀ i,F i 0=PowerSeries.constantCoeff ℂ (v i)) ∧
      ∀ᶠ z in nhds (0:ℂ), ∀ i,
        (ordinaryPointPolynomialShift α t).eval₂ σ z*deriv (F i) z=
          ∑ l,(ordinaryPointPolynomialShift α (U i l)).eval₂ σ z*F l z := by
  classical
  let BK := ordinaryPointClearedMatrix t U α
  let ZK := formalFundamentalMatrix BK
  let ψ : PowerSeries K →+* PowerSeries ℂ := PowerSeries.map σ
  let B := BK.map ψ
  let Z := ZK.map ψ
  let Y := ordinaryPointAnalyticMatrix σ t U α
  let c : Fin r → ℂ := fun j => PowerSeries.constantCoeff ℂ (v j)
  let F : Fin r → ℂ → ℂ := fun i z => ∑ j,Y i j z*c j
  obtain ⟨hZ,hZ0⟩ := ordinaryPoint_mapped_formal_frame t U α σ
  have hrep : ∀ i,v i=∑ j,Z i j*PowerSeries.C ℂ (c j) :=
    powerSeries_solution_eq_frame_initial B Z hZ hZ0 v hv
  obtain ⟨C,hC,hOn⟩ := ordinaryPoint_fundamental_analytic_germs t U α hα σ
  have hAt : ∀ i,HasFPowerSeriesAt (F i)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n (v i))) 0 := by
    intro i
    have hj : ∀ j,HasFPowerSeriesAt (Y i j)
        (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n (Z i j))) 0 := by
      intro j
      simpa only [Z,Matrix.map_apply,ψ,PowerSeries.coeff_map] using (hOn i j).hasFPowerSeriesAt
    rw [hrep i]
    exact hasFPowerSeriesAt_finset_sum_ofScalars Finset.univ
      (fun j z => Y i j z*c j) (fun j => Z i j*PowerSeries.C ℂ (c j))
      (fun j hj' => hasFPowerSeriesAt_mul_ofScalars _ _ _ _ (hj j)
        (by simpa only [Polynomial.eval_C,Polynomial.coe_C] using
          hasFPowerSeriesAt_polynomial_ofScalars (Polynomial.C (c j))))
  have hclear (i l : Fin r) :
      ((ordinaryPointPolynomialShift α t).map σ:PowerSeries ℂ)*B i l=
        ((ordinaryPointPolynomialShift α (U i l)).map σ:PowerSeries ℂ) := by
    have hc : PowerSeries.constantCoeff K (ordinaryPointPolynomialSeries α t) ≠ 0 := by
      rw [ordinaryPointPolynomialSeries_constantCoeff]
      exact hα
    have hk : ordinaryPointPolynomialSeries α t*BK i l=ordinaryPointPolynomialSeries α (U i l) := by
      change ordinaryPointPolynomialSeries α t*
        (ordinaryPointPolynomialSeries α (U i l)*(ordinaryPointPolynomialSeries α t)⁻¹)=_
      calc
        _ = (ordinaryPointPolynomialSeries α t*(ordinaryPointPolynomialSeries α t)⁻¹)*
            ordinaryPointPolynomialSeries α (U i l) := by ring
        _ = _ := by rw [PowerSeries.mul_inv_cancel _ hc,one_mul]
    have hm := congrArg ψ hk
    simpa only [ψ,B,Matrix.map_apply,map_mul,ordinaryPointPolynomialSeries,← Polynomial.polynomial_map_coe] using hm
  have hform : ∀ i,((ordinaryPointPolynomialShift α t).map σ:PowerSeries ℂ)*
      PowerSeries.derivative ℂ (v i)=
      ∑ l,((ordinaryPointPolynomialShift α (U i l)).map σ:PowerSeries ℂ)*v l := by
    intro i
    rw [hv i,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    rw [← mul_assoc]
    change (((ordinaryPointPolynomialShift α t).map σ:PowerSeries ℂ)*B i l)*v l=_
    rw [hclear]
  refine ⟨F,hAt,?_,?_⟩
  · intro i
    have h0 := (hAt i).coeff_zero (fun _ => (1:ℂ))
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq,PowerSeries.coeff_zero_eq_constantCoeff,
      pow_zero,smul_eq_mul,mul_one] using h0.symm
  · have h := ordinary_series_vector_ode_eventually
      ((ordinaryPointPolynomialShift α t).map σ)
      (fun i l => (ordinaryPointPolynomialShift α (U i l)).map σ) v F hAt hform
    simpa only [Polynomial.eval_map] using h

end StrictEUnit
end
