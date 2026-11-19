import OrdinaryGermAlgebra
import SelectedScalarFieldMapTransport

noncomputable section
open scoped Topology BigOperators Matrix
namespace StrictEUnit

theorem hasFPowerSeriesAt_iteratedDeriv_ofScalars
    (f : ℂ → ℂ) (P : PowerSeries ℂ)
    (h : HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n P)) 0)
    (n : ℕ) :
    HasFPowerSeriesAt (iteratedDeriv n f)
      (FormalMultilinearSeries.ofScalars ℂ
        (fun m => PowerSeries.coeff ℂ m ((PowerSeries.derivative ℂ)^[n] P))) 0 := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero, Function.iterate_zero_apply] using h
  | succ n ih =>
    rw [iteratedDeriv_succ, Function.iterate_succ_apply']
    exact hasFPowerSeriesAt_deriv_ofScalars _ _ ih

/-- Formal scalar ODEs with convergent literal series become actual local
analytic identities. No global differentiability or entire premise is used. -/
theorem ordinary_series_scalar_ode_eventually
    (f : ℂ → ℂ) (P : PowerSeries ℂ) (m : ℕ) (p : Fin m → Polynomial ℂ)
    (h : HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n P)) 0)
    (hode : (∑ i, (p i : PowerSeries ℂ) * (PowerSeries.derivative ℂ)^[i.val] P) = 0) :
    ∀ᶠ z in nhds (0:ℂ), (∑ i, (p i).eval z * iteratedDeriv i.val f z) = 0 := by
  have hr := hasFPowerSeriesAt_finset_sum_ofScalars Finset.univ
    (fun i z => (p i).eval z * iteratedDeriv i.val f z)
    (fun i => (p i : PowerSeries ℂ) * (PowerSeries.derivative ℂ)^[i.val] P)
    (fun i hi => hasFPowerSeriesAt_mul_ofScalars _ _ _ _
      (hasFPowerSeriesAt_polynomial_ofScalars (p i))
      (hasFPowerSeriesAt_iteratedDeriv_ofScalars f P h i.val))
  rw [hode] at hr
  have hz : FormalMultilinearSeries.ofScalars ℂ
      (fun n => PowerSeries.coeff ℂ n (0:PowerSeries ℂ)) = 0 := by
    have he : (fun n => PowerSeries.coeff ℂ n (0:PowerSeries ℂ)) = (0:ℕ → ℂ) := by
      funext n
      exact map_zero (PowerSeries.coeff ℂ n)
    rw [he, FormalMultilinearSeries.ofScalars_series_eq_zero_of_scalar_zero]
  rw [hz] at hr
  exact hr.eventually_eq_zero

theorem ordinary_series_matrix_ode_eventually {r : ℕ}
    (t : Polynomial ℂ) (U : Matrix (Fin r) (Fin r) (Polynomial ℂ))
    (Z : Matrix (Fin r) (Fin r) (PowerSeries ℂ))
    (Y : Matrix (Fin r) (Fin r) (ℂ → ℂ))
    (hY : ∀ i j, HasFPowerSeriesAt (Y i j)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n (Z i j))) 0)
    (hode : ∀ i j, (t:PowerSeries ℂ) * PowerSeries.derivative ℂ (Z i j) =
      ∑ l, (U i l : PowerSeries ℂ)*Z l j) :
    ∀ᶠ z in nhds (0:ℂ), ∀ i j,
      t.eval z * deriv (Y i j) z = ∑ l, (U i l).eval z * Y l j z := by
  apply Filter.eventually_all.2
  intro i
  apply Filter.eventually_all.2
  intro j
  have hl := hasFPowerSeriesAt_mul_ofScalars (fun z => t.eval z) (deriv (Y i j)) _ _
    (hasFPowerSeriesAt_polynomial_ofScalars t)
    (hasFPowerSeriesAt_deriv_ofScalars (Y i j) (Z i j) (hY i j))
  have hr := hasFPowerSeriesAt_finset_sum_ofScalars Finset.univ
    (fun l z => (U i l).eval z * Y l j z)
    (fun l => (U i l : PowerSeries ℂ)*Z l j)
    (fun l hl => hasFPowerSeriesAt_mul_ofScalars _ _ _ _
      (hasFPowerSeriesAt_polynomial_ofScalars (U i l)) (hY l j))
  rw [hode i j] at hl
  exact eventually_eq_of_same_ordinary_series _ _ _ hl hr

/-- The actual summed entries, whose convergence is proved from the SAME
constructed matrix and coefficient house bounds. -/
def ordinaryPointAnalyticMatrix
    {K : Type*} [Field K] [NumberField K] {r : ℕ}
    (σ : K →+* ℂ) (t : Polynomial K)
    (U : Matrix (Fin r) (Fin r) (Polynomial K)) (α : K) :
    Matrix (Fin r) (Fin r) (ℂ → ℂ) :=
  fun i j => ordinaryGermSum (fun n => σ (PowerSeries.coeff K n
    (formalFundamentalMatrix (ordinaryPointClearedMatrix t U α) i j)))

/-- The SAME constructed formal matrix is realized by genuine analytic
functions, normalized at zero and solving its actual shifted cleared ODE. -/
theorem ordinaryPoint_actual_cleared_system
    {K : Type*} [Field K] [NumberField K] {r : ℕ}
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K)) (α : K)
    (hα : t.eval α ≠ 0) (σ : K →+* ℂ) :
    let Y := ordinaryPointAnalyticMatrix σ t U α
    ∃ C : ℝ, ∃ hC : 1 ≤ C,
      (∀ i j, HasFPowerSeriesOnBall (Y i j)
        (FormalMultilinearSeries.ofScalars ℂ (fun n => σ (PowerSeries.coeff K n
          (formalFundamentalMatrix (ordinaryPointClearedMatrix t U α) i j))))
        0 (ordinaryGermRadius C hC : ENNReal)) ∧
      (∀ i j, Y i j 0 = if i=j then 1 else 0) ∧
      ∀ᶠ z in nhds (0:ℂ), ∀ i j,
        (ordinaryPointPolynomialShift α t).eval₂ σ z * deriv (Y i j) z =
          ∑ l, (ordinaryPointPolynomialShift α (U i l)).eval₂ σ z * Y l j z := by
  classical
  let Z := formalFundamentalMatrix (ordinaryPointClearedMatrix t U α)
  let ZC : Matrix (Fin r) (Fin r) (PowerSeries ℂ) := fun i j => PowerSeries.map σ (Z i j)
  let Y := ordinaryPointAnalyticMatrix σ t U α
  let tα := ordinaryPointPolynomialShift α t
  let Uα : Matrix (Fin r) (Fin r) (Polynomial K) := fun i l => ordinaryPointPolynomialShift α (U i l)
  obtain ⟨C,hC,hOn⟩ := ordinaryPoint_fundamental_analytic_germs t U α hα σ
  have hAt : ∀ i j, HasFPowerSeriesAt (Y i j)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n (ZC i j))) 0 := by
    intro i j
    simpa only [ZC, PowerSeries.coeff_map] using (hOn i j).hasFPowerSeriesAt
  have hformal : ∀ i j, ((tα.map σ):PowerSeries ℂ) * PowerSeries.derivative ℂ (ZC i j) =
      ∑ l, ((Uα i l).map σ : PowerSeries ℂ)*ZC l j := by
    intro i j
    have hK := ordinaryPointClearedMatrix_fundamental_cleared t U α hα i j
    have hm := congrArg (PowerSeries.map σ) hK
    change PowerSeries.map σ ((tα:PowerSeries K)*PowerSeries.derivative K (Z i j)) =
      PowerSeries.map σ (∑ l,(Uα i l:PowerSeries K)*Z l j) at hm
    simpa only [map_mul, map_sum, ordinaryBorel_map_derivative,
      ← Polynomial.polynomial_map_coe] using hm
  refine ⟨C,hC,hOn,?_,?_⟩
  · intro i j
    have h0 := (hOn i j).coeff_zero (fun _ => (1:ℂ))
    have hz := congrArg (fun M : Matrix (Fin r) (Fin r) K => M i j)
      (formalFundamentalMatrix_constantCoeff (ordinaryPointClearedMatrix t U α))
    change PowerSeries.constantCoeff K (Z i j) = (1:Matrix (Fin r) (Fin r) K) i j at hz
    change Y i j 0 = _
    have he : Y i j 0 = σ (PowerSeries.coeff K 0 (Z i j)) := by
      simpa only [FormalMultilinearSeries.ofScalars_apply_eq, pow_zero,
        smul_eq_mul, mul_one] using h0.symm
    rw [he,PowerSeries.coeff_zero_eq_constantCoeff,hz,Matrix.one_apply]
    split_ifs <;> simp
  · have h := ordinary_series_matrix_ode_eventually (tα.map σ)
      (fun i l => (Uα i l).map σ) ZC Y hAt hformal
    simpa only [Polynomial.eval_map] using h

end StrictEUnit
end
