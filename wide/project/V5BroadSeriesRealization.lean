import V5BroadActualData
import V5BroadDivisionTail
import Stage41GeometricEntireSeries

noncomputable section
open scoped BigOperators Topology
open Filter
namespace StrictEUnit

/-- Broad factorial growth (one exponent at most one half is enough) gives
absolute convergence at every radius. -/
theorem v5_broad_factorial_norm_summable (a : ℕ → ℂ) (C η : ℝ)
    (hC : 1 ≤ C) (hη : η ≤ 1/2)
    (ha : ∀ n, ‖a n‖ ≤ C^(n+1) * (n.factorial : ℝ)^η) (r : NNReal) :
    Summable (fun n => ‖a n / (n.factorial : ℂ)‖ * (r : ℝ)^n) := by
  let R : ℝ := max 1 (r : ℝ)
  let D := C*R
  have hR : 1 ≤ R := le_max_left _ _
  have hD : 1 ≤ D := one_le_mul_of_one_le_of_one_le hC hR
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hnon (n : ℕ) : 0 ≤ v5BroadTailMajorant D η n := by
    unfold v5BroadTailMajorant D R
    positivity
  have hs : Summable (v5BroadTailMajorant D η) := by
    obtain ⟨N,hN⟩ := exists_nat_ge ((2*D)^2)
    apply summable_of_ratio_norm_eventually_le (r := 1/2) (by norm_num)
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [Real.norm_of_nonneg (hnon (n+1)), Real.norm_of_nonneg (hnon n), mul_comm (1/2 : ℝ)]
    exact v5_broad_tail_majorant_step hD hη n (hN.trans (by exact_mod_cast (show N ≤ n+1 by omega)))
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ hs
  intro n
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have he : C^(n+1)*(r : ℝ)^n ≤ D^(n+1) := by
    rw [show D^(n+1) = C^(n+1)*R^(n+1) by simp [D,mul_pow]]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (pow_le_pow_left₀ r.coe_nonneg (le_max_right _ _) n).trans
      (pow_le_pow_right₀ hR (by omega))
  rw [norm_div, Complex.norm_natCast, div_mul_eq_mul_div, v5BroadTailMajorant]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    ‖a n‖ * (r : ℝ)^n ≤ (C^(n+1)*(n.factorial : ℝ)^η)*(r : ℝ)^n :=
      mul_le_mul_of_nonneg_right (ha n) (by positivity)
    _ = (C^(n+1)*(r : ℝ)^n)*(n.factorial : ℝ)^η := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right he (by positivity)

/-- The sums of the literal source series define an entire complex function,
without selecting an arbitrary realization. -/
theorem v5_broad_series_hasSum_entire (a : ℕ → AlgebraicComplex)
    (ha : V5BroadAlgebraicArithmetic a) :
    Differentiable ℂ (exponentialGeneratingFunction (fun n => (a n : ℂ))) ∧
    ∀ z, HasSum (fun n => (a n : ℂ)*z^n/(n.factorial : ℂ))
      (exponentialGeneratingFunction (fun n => (a n : ℂ)) z) := by
  obtain ⟨C,hC,_,_,_,hconj,_⟩ := ha (1/2) (by norm_num)
  let b : ℕ → ℂ := fun n => (a n : ℂ)
  have hs (r : NNReal) := v5_broad_factorial_norm_summable b C (1/2) hC le_rfl
    (hconj (algebraicClosure ℚ ℂ).val) r
  have hseries (z : ℂ) : HasSum (fun n => b n*z^n/(n.factorial : ℂ))
      (exponentialGeneratingFunction b z) := by
    apply Summable.hasSum
    apply (show Summable fun n => ‖b n*z^n/(n.factorial : ℂ)‖ from ?_).of_norm
    simpa only [norm_div, norm_mul, norm_pow, Complex.norm_natCast, coe_nnnorm,
      div_mul_eq_mul_div] using hs ‖z‖₊
  have hrad : (stage41_factorialMultilinearSeries b).radius = ⊤ := by
    apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
    intro r
    simpa only [stage41_factorialMultilinearSeries, ContinuousMultilinearMap.norm_mkPiRing]
      using hs r
  have hp : HasFPowerSeriesOnBall (exponentialGeneratingFunction b)
      (stage41_factorialMultilinearSeries b) 0 ⊤ := by
    refine ⟨by rw [hrad], by simp, ?_⟩
    intro z _
    convert hseries z using 1
    · funext n
      simp only [stage41_factorialMultilinearSeries, ContinuousMultilinearMap.mkPiRing_apply,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      ring
    · simp
  exact ⟨fun z => (hp.analyticAt_of_mem (by simp)).differentiableAt, hseries⟩

/-- A literal factorial formal ODE suffices for the analytically realized
series; the same tuple is used in the concluded analytic equation. -/
theorem v5_broad_series_realization (a : ℕ → AlgebraicComplex)
    (ha : V5BroadAlgebraicArithmetic a)
    (m : ℕ) (p : Fin (m+1) → Polynomial AlgebraicComplex) (hp : ∃ i, p i ≠ 0)
    (hode : ∑ i, (p i : PowerSeries AlgebraicComplex) *
      (PowerSeries.derivative AlgebraicComplex)^[i.val]
        (PowerSeries.mk (fun n => a n / (n.factorial : AlgebraicComplex))) = 0) :
    V5IsBroadEFunction (exponentialGeneratingFunction (fun n => (a n : ℂ))) := by
  classical
  obtain ⟨hd,hs⟩ := v5_broad_series_hasSum_entire a ha
  let f : entireFunctionAlgebra := ⟨_,hd⟩
  let φ := (algebraicClosure ℚ ℂ).val.toRingHom
  let P : ℕ → Polynomial ℂ := fun j => if hj : j < m+1 then (p ⟨j,hj⟩).map φ else 0
  have hP (i : Fin (m+1)) : P i.val = (p i).map φ := dif_pos i.isLt
  have ht : PowerSeries.map φ
      (PowerSeries.mk (fun n => a n / (n.factorial : AlgebraicComplex))) =
        entireTaylorAlgHom f := by
    ext n
    rw [entireTaylorAlgHom_apply, coeff_entireFormalTaylor]
    simp only [PowerSeries.coeff_map, PowerSeries.coeff_mk, map_div₀, map_natCast]
    symm
    apply entireCauchyCoefficient_eq_of_hasSum hd
    intro z
    convert hs z using 1
    funext j
    change φ (a j)/(j.factorial : ℂ)*z^j = φ (a j)*z^j / (j.factorial : ℂ)
    ring
  have hm := congrArg (PowerSeries.map φ) hode
  rw [map_sum, map_zero] at hm
  simp only [map_mul, ordinaryBorel_map_iterate_derivative, ← Polynomial.polynomial_map_coe, ht] at hm
  have hrow : v5FormalRow P m (entireTaylorAlgHom f) = 0 := by
    rw [v5FormalRow, ← Fin.sum_univ_eq_sum_range]
    simpa only [hP] using hm
  refine ⟨a,hd,hs,⟨m,p,hp,?_⟩,ha⟩
  intro z
  have h := (v5_formalRow_eq_zero_iff f P m).mp hrow z
  change (∑ j ∈ Finset.range (m+1), (P j).eval z * iteratedDeriv j f.val z) = 0 at h
  rw [← Fin.sum_univ_eq_sum_range] at h
  simpa only [hP, Polynomial.eval_map] using h

#print axioms v5_broad_factorial_norm_summable
#print axioms v5_broad_series_hasSum_entire
#print axioms v5_broad_series_realization
end StrictEUnit
end
