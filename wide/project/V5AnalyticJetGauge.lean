import V5OrdinaryJetGauge
import V5ShiftedAnalyticJets
import V5JetCoordinateBasis

noncomputable section
open scoped Topology BigOperators
open Filter
namespace StrictEUnit
variable {K : Type*} [Field K]

def v5NormalizedScalarCompanion (p : ℕ → Polynomial K) (n : ℕ) :
    Matrix (Fin n) (Fin n) (RatFunc K) :=
  minimalDerivativeCompanion n (fun j =>
    -(algebraMap (Polynomial K) (RatFunc K) (p n))⁻¹ *
      algebraMap (Polynomial K) (RatFunc K) (p j.val))

theorem v5_normalized_scalar_companion_map {L : Type*} [Field L]
    (φ : RatFunc K →+* LaurentSeries L) (p : ℕ → Polynomial K) (n : ℕ) :
    (v5NormalizedScalarCompanion p n).map φ =
      v5LaurentCompanion n (fun j => φ (algebraMap (Polynomial K) (RatFunc K) (p j))) := by
  funext i j
  simp [v5NormalizedScalarCompanion, Matrix.map_apply, minimalDerivativeCompanion,
    v5LaurentCompanion, apply_ite φ]

/-- A nonvanishing evaluation functional in the local analytic solution
space produces an ordinary rational system with one coordinate literally
equal to the original solution function. The equation is allowed to be
singular at the marked point. -/
theorem v5_analytic_scalar_jetGauge_ordinary {n : ℕ} (hn : 0 < n)
    (e : K →+* ℂ) (α : K) (p : ℕ → Polynomial K) (hp : p n ≠ 0)
    (u : Fin n → ℂ → ℂ)
    (hu : ∀ i, AnalyticAt ℂ (u i) (e α)) (hind : v5FiniteGermIndependent (e α) u)
    (hode : ∀ i, ∀ᶠ z in 𝓝 (e α),
      v5RowResidual (u i) n (fun j => (p j).map e) z = 0)
    (hval : ∃ i, u i (e α) ≠ 0) :
    ∃ d : Fin n → ℕ, (∃ i, d i = 0) ∧
      let A := v5NormalizedScalarCompanion p n
      let R := v5SelectedCovariantRows A ⟨0,hn⟩ d
      R.det ≠ 0 ∧ ∃ T : Polynomial K, T.eval α ≠ 0 ∧
        ∃ U : Matrix (Fin n) (Fin n) (Polynomial K), ∀ i j,
        algebraMap (Polynomial K) (RatFunc K) (U i j) =
          algebraMap (Polynomial K) (RatFunc K) T * v5RationalJetGauge A R i j := by
  classical
  let φ := v5_extensionOrdinaryRationalMap e α
  let ψ := HahnSeries.ofPowerSeries ℤ ℂ
  let q := v5ShiftPolynomialRow (fun j => (p j).map e) (e α)
  let f : Fin n → ℂ → ℂ := fun i z => u i (z + e α)
  have hfa (i : Fin n) : AnalyticAt ℂ (f i) 0 := v5_shift_analyticAt (hu i)
  have hfo (i : Fin n) : ∀ᶠ z in 𝓝 (0 : ℂ), v5RowResidual (f i) n q z = 0 := by
    have ht : Tendsto (fun z : ℂ => z + e α) (𝓝 0) (𝓝 (e α)) := by
      simpa [ContinuousAt] using (continuousAt_id (x := (0:ℂ))).add
        (show ContinuousAt (fun _ : ℂ => e α) 0 from continuousAt_const)
    filter_upwards [ht.eventually (hode i)] with z hz
    exact (v5_shift_row_residual _ n (u i) (e α) z).trans hz
  choose s hs using fun i => analyticAt_has_ordinary_series (f i) (hfa i)
  have hform (i : Fin n) : v5ScalarODE q (n+1) (s i) = 0 :=
    v5_formal_ode_from_analytic_germ q _ _ (hs i) (hfo i)
  obtain ⟨d,hd,hdet⟩ := v5_analytic_jet_det_retaining_zero u (e α) hu hind hval
  refine ⟨d,hd,?_⟩
  let Y : Matrix (Fin n) (Fin n) (LaurentSeries ℂ) := fun i j =>
    v5LaurentJet n (ψ (s j)) i
  have hq (j : ℕ) : φ (algebraMap (Polynomial K) (RatFunc K) (p j)) =
      ψ (q j : PowerSeries ℂ) := v5_extensionOrdinaryRationalMap_polynomial e α (p j)
  have hqne : φ (algebraMap (Polynomial K) (RatFunc K) (p n)) ≠ 0 :=
    (map_ne_zero_iff φ φ.injective).mpr (RatFunc.algebraMap_ne_zero hp)
  have hsol (j : Fin n) : ∑ k ∈ Finset.range (n+1), φ
      (algebraMap (Polynomial K) (RatFunc K) (p k)) *
      (laurentOrdinaryDerivation : LaurentSeries ℂ → LaurentSeries ℂ)^[k] (ψ (s j)) = 0 := by
    have h := congrArg ψ (hform j)
    simpa only [hq, ψ, v5ScalarODE, map_sum, map_mul, map_zero,
      laurentOrdinaryDerivation_iterate_ofPowerSeries] using h
  have hY : v5LaurentMatrixDerivative Y = (v5NormalizedScalarCompanion p n).map φ * Y := by
    rw [v5_normalized_scalar_companion_map]
    funext i j
    exact v5_laurent_jet_system n _ hqne (ψ (s j)) (hsol j) i
  have hjet : (fun i j : Fin n => PowerSeries.constantCoeff ℂ
      ((PowerSeries.derivative ℂ)^[d i] (s j))) =
      fun i j => iteratedDeriv (d i) (u j) (e α) := by
    funext i j
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    have he := v5_series_coeff_zero_of_realized _ _
      (hasFPowerSeriesAt_iteratedDeriv_ofScalars _ _ (hs j) (d i))
    rw [he]
    change iteratedDeriv (d i) (fun z => u j (z + e α)) 0 = _
    rw [iteratedDeriv_comp_add_const]
    simp only [zero_add]
  exact v5_selected_formal_jets_ordinary e α (v5NormalizedScalarCompanion p n)
    ⟨0,hn⟩ d s Y hY (fun _ => rfl) (by rwa [hjet])

#print axioms v5_normalized_scalar_companion_map
#print axioms v5_analytic_scalar_jetGauge_ordinary
end StrictEUnit
