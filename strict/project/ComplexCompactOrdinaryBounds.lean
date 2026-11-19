import ComplexOrdinaryGermExtension
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Topology.Order.Compact

noncomputable section
open scoped Topology BigOperators Matrix
namespace StrictEUnit

/-- Coefficients of the literal polynomial translation vary continuously with
the complex center. No infinite series substitution is used. -/
theorem continuous_ordinaryPointPolynomialShift_coeff (p : Polynomial ℂ) (k : ℕ) :
    Continuous (fun β : ℂ => (ordinaryPointPolynomialShift β p).coeff k) := by
  have he (β : ℂ) : (ordinaryPointPolynomialShift β p).coeff k=
      (Polynomial.hasseDeriv k p).eval β := by
    rw [ordinaryPointPolynomialShift_apply,← Polynomial.taylor_apply,Polynomial.taylor_coeff]
  simp_rw [he]
  exact (Polynomial.hasseDeriv k p).continuous

def complexOrdinaryCenterMajorant {r : ℕ} (t : Polynomial ℂ)
    (U : Matrix (Fin r) (Fin r) (Polynomial ℂ)) (D : ℕ) (β : ℂ) : ℝ :=
  clearedSystemNormConstant (ordinaryPointPolynomialShift β t)
    (fun i l => ordinaryPointPolynomialShift β (U i l)) D

theorem complexOrdinaryCenterMajorant_one_le {r : ℕ} (t : Polynomial ℂ)
    (U : Matrix (Fin r) (Fin r) (Polynomial ℂ)) (D : ℕ) (β : ℂ) :
    1 ≤ complexOrdinaryCenterMajorant t U D β :=
  clearedSystemNormConstant_one_le _ _ _

/-- The explicit recurrence majorant is continuous on the SAME regular locus. -/
theorem complexOrdinaryCenterMajorant_continuousOn {r : ℕ}
    (t : Polynomial ℂ) (U : Matrix (Fin r) (Fin r) (Polynomial ℂ)) (D : ℕ)
    (s : Set ℂ) (hs : ∀ β ∈ s,t.eval β ≠ 0) :
    ContinuousOn (complexOrdinaryCenterMajorant t U D) s := by
  have hi : ContinuousOn (fun β : ℂ => ‖(t.eval β)⁻¹‖) s :=
    (t.continuousOn.inv₀ hs).norm
  have ht : Continuous (fun β : ℂ =>
      clearedSystemTailNorm (ordinaryPointPolynomialShift β t) D) := by
    exact continuous_finset_sum _ (fun k hk =>
      (continuous_ordinaryPointPolynomialShift_coeff t (k.val+1)).norm)
  have hU : Continuous (fun β : ℂ => clearedSystemMatrixNorm
      (fun i l => ordinaryPointPolynomialShift β (U i l)) D) := by
    exact continuous_finset_sum _ (fun i hi => continuous_finset_sum _ (fun l hl =>
      continuous_finset_sum _ (fun k hk =>
        (continuous_ordinaryPointPolynomialShift_coeff (U i l) k.val).norm)))
  have he (β : ℂ) : complexOrdinaryCenterMajorant t U D β=
      1+‖(t.eval β)⁻¹‖*(clearedSystemTailNorm (ordinaryPointPolynomialShift β t) D+
        clearedSystemMatrixNorm (fun i l => ordinaryPointPolynomialShift β (U i l)) D) := by
    unfold complexOrdinaryCenterMajorant clearedSystemNormConstant
    rw [show (ordinaryPointPolynomialShift β t).coeff 0=t.eval β from
      ordinaryPointPolynomialSeries_constantCoeff β t]
  rw [show complexOrdinaryCenterMajorant t U D=(fun β : ℂ =>
      1+‖(t.eval β)⁻¹‖*(clearedSystemTailNorm (ordinaryPointPolynomialShift β t) D+
        clearedSystemMatrixNorm (fun i l => ordinaryPointPolynomialShift β (U i l)) D)) from funext he]
  exact continuousOn_const.add (hi.mul (ht.add hU).continuousOn)

/-- A compact subset of the SAME regular locus has an internally derived
uniform coefficient majorant. No uniformity premise is supplied. -/
theorem complexOrdinaryCenterMajorant_bounded_on_compact {r : ℕ}
    (t : Polynomial ℂ) (U : Matrix (Fin r) (Fin r) (Polynomial ℂ)) (D : ℕ)
    (s : Set ℂ) (hcompact : IsCompact s) (hs : ∀ β ∈ s,t.eval β ≠ 0) :
    ∃ M : ℝ,1 ≤ M ∧ ∀ β ∈ s,complexOrdinaryCenterMajorant t U D β ≤ M := by
  obtain ⟨B,hB⟩ := hcompact.bddAbove_image
    (complexOrdinaryCenterMajorant_continuousOn t U D s hs)
  refine ⟨max 1 B,le_max_left _ _,?_⟩
  intro β hβ
  exact (hB (Set.mem_image_of_mem _ hβ)).trans (le_max_right _ _)

/-- The explicit SAME normalized frames have a common coefficient bound at
EVERY center of a compact regular set. This is analytic uniformity only. -/
theorem complexOrdinaryPoint_uniform_coeff_bound_on_compact {r : ℕ}
    (t : Polynomial ℂ) (U : Matrix (Fin r) (Fin r) (Polynomial ℂ))
    (s : Set ℂ) (hcompact : IsCompact s) (hs : ∀ β ∈ s,t.eval β ≠ 0) :
    ∃ M : ℝ,1 ≤ M ∧ ∀ β ∈ s, ∀ n i j,
      ‖PowerSeries.coeff ℂ n
        (formalFundamentalMatrix (ordinaryPointClearedMatrix t U β) i j)‖ ≤ M^n := by
  obtain ⟨D,ht,hU⟩ := complex_exists_clearedSystem_common_degree t U
  obtain ⟨M,hM,hmajor⟩ := complexOrdinaryCenterMajorant_bounded_on_compact t U D s hcompact hs
  refine ⟨M,hM,?_⟩
  intro β hβ n i j
  let tβ := ordinaryPointPolynomialShift β t
  let Uβ : Matrix (Fin r) (Fin r) (Polynomial ℂ) :=
    fun i l => ordinaryPointPolynomialShift β (U i l)
  let Z := formalFundamentalMatrix (ordinaryPointClearedMatrix t U β)
  have h0 : tβ.coeff 0 ≠ 0 := by
    rw [show tβ.coeff 0=t.eval β from ordinaryPointPolynomialSeries_constantCoeff β t]
    exact hs β hβ
  have htβ : tβ.natDegree ≤ D := by rw [ordinaryPointPolynomialShift_natDegree];exact ht
  have hUβ : ∀ i l,(Uβ i l).natDegree ≤ D := by
    intro i l
    rw [ordinaryPointPolynomialShift_natDegree]
    exact hU i l
  have hb := clearedPolynomialSystem_coeff_norm_bound tβ Uβ Z h0 D htβ hUβ
    (ordinaryPointClearedMatrix_fundamental_cleared t U β (hs β hβ))
    (formalFundamentalMatrix_constantCoeff (ordinaryPointClearedMatrix t U β)) n i j
  exact hb.trans (pow_le_pow_left₀
    (le_trans zero_le_one (complexOrdinaryCenterMajorant_one_le t U D β)) (hmajor β hβ) n)

/-- Uniform actual analytic disks for the SAME frames over any compact subset
of the regular locus, including the image of any regular compact path. -/
theorem complexOrdinaryPoint_uniform_analytic_disks_on_compact {r : ℕ}
    (t : Polynomial ℂ) (U : Matrix (Fin r) (Fin r) (Polynomial ℂ))
    (s : Set ℂ) (hcompact : IsCompact s) (hs : ∀ β ∈ s,t.eval β ≠ 0) :
    ∃ M : ℝ,∃ hM : 1 ≤ M, ∀ β ∈ s, ∀ i j,
      HasFPowerSeriesOnBall (complexOrdinaryAnalyticMatrix t U β i j)
        (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff ℂ n
          (formalFundamentalMatrix (ordinaryPointClearedMatrix t U β) i j)))
        0 (ordinaryGermRadius M hM : ENNReal) := by
  obtain ⟨M,hM,hbound⟩ := complexOrdinaryPoint_uniform_coeff_bound_on_compact t U s hcompact hs
  exact ⟨M,hM,fun β hβ i j => ordinaryGerm_hasFPowerSeriesOnBall _ M hM
    (fun n => hbound β hβ n i j)⟩

end StrictEUnit
end
