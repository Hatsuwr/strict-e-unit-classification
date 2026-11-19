import V5AnalyticWronskianBridge

noncomputable section
open scoped Topology
open Filter
namespace StrictEUnit

def v5ShiftPolynomialRow {K : Type*} [CommSemiring K] (p : ℕ → Polynomial K) (c : K) :
    ℕ → Polynomial K := fun j => (p j).comp (Polynomial.X+Polynomial.C c)

theorem v5_shift_row_map {K L : Type*} [CommSemiring K] [CommSemiring L]
    (φ : K →+* L) (p : ℕ → Polynomial K) (c : K) (j : ℕ) :
    (v5ShiftPolynomialRow p c j).map φ =
      v5ShiftPolynomialRow (fun i => (p i).map φ) (φ c) j := by
  simp [v5ShiftPolynomialRow, Polynomial.map_comp]

private theorem v5_tendsto_shift (c : ℂ) :
    Tendsto (fun z : ℂ => z+c) (𝓝 0) (𝓝 c) := by
  simpa [ContinuousAt] using (continuousAt_id (x := (0:ℂ))).add continuousAt_const (g := fun _ => c)

theorem v5_shift_row_residual (p : ℕ → Polynomial ℂ) (n : ℕ)
    (f : ℂ → ℂ) (c z : ℂ) :
    v5RowResidual (fun t => f (t+c)) n (v5ShiftPolynomialRow p c) z =
      v5RowResidual f n p (z+c) := by
  unfold v5RowResidual
  apply Finset.sum_congr rfl
  intro j _
  change (v5ShiftPolynomialRow p c j).eval z * iteratedDeriv j (fun t => f (t+c)) z =
    (p j).eval (z+c) * iteratedDeriv j f (z+c)
  rw [show iteratedDeriv j (fun t => f (t+c)) z = iteratedDeriv j f (z+c) from
    congrFun (iteratedDeriv_comp_add_const j f c) z]
  simp [v5ShiftPolynomialRow, Polynomial.eval_comp]

theorem v5_shift_analyticAt {f : ℂ → ℂ} {c : ℂ} (h : AnalyticAt ℂ f c) :
    AnalyticAt ℂ (fun z => f (z+c)) 0 := by
  exact h.comp_of_eq (analyticAt_id.add analyticAt_const) (by simp)

theorem v5_shift_independent {n : ℕ} (u : Fin n → ℂ → ℂ) (c : ℂ)
    (h : v5FiniteGermIndependent c u) :
    v5FiniteGermIndependent 0 (fun i z => u i (z+c)) := by
  intro a ha
  apply h a
  have ht : Tendsto (fun z : ℂ => z-c) (𝓝 c) (𝓝 0) := by
    simpa [ContinuousAt] using (continuousAt_id (x := c)).sub continuousAt_const (g := fun _ => c)
  have he := ht.eventually ha
  simpa only [v5WeightedGerm, sub_add_cancel] using he

theorem v5_series_coeff_zero_of_realized (f : ℂ → ℂ) (s : PowerSeries ℂ)
    (hs : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ
      (fun k => PowerSeries.coeff ℂ k s)) 0) :
    PowerSeries.coeff ℂ 0 s = f 0 := by
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq, Finset.prod_empty, Finset.univ_eq_empty,
    smul_eq_mul, one_mul, pow_zero, mul_one] using hs.coeff_zero (fun _ => (1:ℂ))

/-- An exact analytic germ family at any mark supplies a literal formal
solution family after shifting the same operator; the Wronskian is nonzero. -/
theorem v5_formal_family_from_analytic_germs {n : ℕ}
    (p : ℕ → Polynomial ℂ) (hp : p n ≠ 0) (u : Fin n → ℂ → ℂ) (c : ℂ)
    (hu : ∀ i, AnalyticAt ℂ (u i) c) (hind : v5FiniteGermIndependent c u)
    (hode : ∀ i, ∀ᶠ z in 𝓝 c, v5RowResidual (u i) n p z = 0) :
    ∃ s : Fin n → PowerSeries ℂ, (v5FormalJetMatrix s).det ≠ 0 ∧
      ∀ i, v5ScalarODE (v5ShiftPolynomialRow p c) (n+1) (s i) = 0 ∧
        PowerSeries.coeff ℂ 0 (s i) = u i c := by
  classical
  let f : Fin n → ℂ → ℂ := fun i z => u i (z+c)
  let q := v5ShiftPolynomialRow p c
  have hq : q n ≠ 0 := Polynomial.comp_X_add_C_ne_zero_iff.mpr hp
  have hfa (i : Fin n) : AnalyticAt ℂ (f i) 0 := v5_shift_analyticAt (hu i)
  have hfi : v5FiniteGermIndependent 0 f := v5_shift_independent u c hind
  have hfo (i : Fin n) : ∀ᶠ z in 𝓝 (0:ℂ), v5RowResidual (f i) n q z = 0 := by
    filter_upwards [(v5_tendsto_shift c).eventually (hode i)] with z hz
    exact (v5_shift_row_residual p n (u i) c z).trans hz
  choose s hs using fun i => analyticAt_has_ordinary_series (f i) (hfa i)
  refine ⟨s, v5_formal_jet_det_ne_zero_from_analytic f s hs
    (v5_analytic_jet_det_frequently_ne_zero q hq f hfa hfi hfo), fun i => ?_⟩
  refine ⟨v5_formal_ode_from_analytic_germ q _ _ (hs i) (hfo i),?_⟩
  simpa only [f,zero_add] using v5_series_coeff_zero_of_realized _ _ (hs i)

#print axioms v5_shift_row_map
#print axioms v5_formal_family_from_analytic_germs
end StrictEUnit
end
