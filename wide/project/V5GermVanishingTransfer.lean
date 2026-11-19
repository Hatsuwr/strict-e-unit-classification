import V5ShiftedAnalyticJets
import V5FormalWronskianSpan
import V5BroadRationalVanishing

noncomputable section
open scoped Topology BigOperators
open Filter
namespace StrictEUnit

/-- A full independent holomorphic family vanishing at the mark forces the
constant term of every formal solution of the shifted row to be zero. -/
theorem v5_formal_scalar_zero_of_vanishing_analytic_family {n : ℕ} (hn : 0 < n)
    (p : ℕ → Polynomial ℂ) (hp : p n ≠ 0) (u : Fin n → ℂ → ℂ) (c : ℂ)
    (hu : ∀ i, AnalyticAt ℂ (u i) c) (hind : v5FiniteGermIndependent c u)
    (hode : ∀ i, ∀ᶠ z in 𝓝 c, v5RowResidual (u i) n p z = 0)
    (hzero : ∀ i, u i c = 0) (y : PowerSeries ℂ)
    (hy : v5ScalarODE (v5ShiftPolynomialRow p c) (n+1) y = 0) :
    PowerSeries.coeff ℂ 0 y = 0 := by
  obtain ⟨s,hd,hs⟩ := v5_formal_family_from_analytic_germs p hp u c hu hind hode
  have he :
      Matrix.det (fun i j : Fin n => HahnSeries.ofPowerSeries ℤ ℂ
        ((PowerSeries.derivative ℂ)^[i.val] (s j))) ≠ 0 := by
    have heq : Matrix.det (fun i j : Fin n => HahnSeries.ofPowerSeries ℤ ℂ
        ((PowerSeries.derivative ℂ)^[i.val] (s j))) =
        HahnSeries.ofPowerSeries ℤ ℂ (v5FormalJetMatrix s).det := by
      exact (RingHom.map_det (HahnSeries.ofPowerSeries ℤ ℂ) (v5FormalJetMatrix s)).symm
    rw [heq]
    exact fun h => hd (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ) (by simpa only [map_zero] using h))
  obtain ⟨a,ha⟩ := v5_formal_scalar_wronskian_span n hn (v5ShiftPolynomialRow p c)
    (Polynomial.comp_X_add_C_ne_zero_iff.mpr hp) s y (fun i => (hs i).1) hy he
  rw [ha, map_sum]
  simp only [PowerSeries.coeff_mul_C, fun i => (hs i).2, hzero, zero_mul, Finset.sum_const_zero]

/-- After an alternate coefficient embedding, the same zero condition holds
for all formal solutions at the corresponding mark. Only coefficients are
mapped; the analytic germs themselves are never conjugated. -/
theorem v5_formal_scalar_zero_under_alternate_embedding
    {K : Type*} [Field K] [CharZero K] {n : ℕ} (hn : 0 < n)
    (φ ψ : K →+* ℂ) (p : ℕ → Polynomial K) (hp : p n ≠ 0)
    (c : K) (u : Fin n → ℂ → ℂ)
    (hu : ∀ i, AnalyticAt ℂ (u i) (φ c)) (hind : v5FiniteGermIndependent (φ c) u)
    (hode : ∀ i, ∀ᶠ z in 𝓝 (φ c),
      v5RowResidual (u i) n (fun j => (p j).map φ) z = 0)
    (hzero : ∀ i, u i (φ c) = 0) (y : PowerSeries ℂ)
    (hy : v5ScalarODE (v5ShiftPolynomialRow (fun j => (p j).map ψ) (ψ c)) (n+1) y = 0) :
    PowerSeries.coeff ℂ 0 y = 0 := by
  classical
  let q := v5ShiftPolynomialRow p c
  let D := (Finset.range (n+1)).sup (fun j => (q j).natDegree)
  have hdeg (j : ℕ) (hj : j < n+1) : (q j).natDegree ≤ D :=
    Finset.le_sup (f := fun i => (q i).natDegree) (Finset.mem_range.mpr hj)
  have hne : ∃ j < n+1, q j ≠ 0 := ⟨n,by omega,Polynomial.comp_X_add_C_ne_zero_iff.mpr hp⟩
  refine v5_scalar_formal_constant_zero_across_maps φ ψ q (n+1) D hdeg hne ?_ y ?_
  · intro x hx
    simp only [q,v5_shift_row_map] at hx
    exact v5_formal_scalar_zero_of_vanishing_analytic_family hn _
      ((Polynomial.map_ne_zero_iff φ.injective).mpr hp) u (φ c) hu hind hode hzero x hx
  · simpa only [q,v5_shift_row_map] using hy

/-- In particular every analytic solution of the coefficient-conjugate
operator vanishes at the conjugate mark, provided the full original analytic
family vanishes. This makes no claim from the vanishing of just one solution. -/
theorem v5_analytic_scalar_zero_under_alternate_embedding
    {K : Type*} [Field K] [CharZero K] {n : ℕ} (hn : 0 < n)
    (φ ψ : K →+* ℂ) (p : ℕ → Polynomial K) (hp : p n ≠ 0)
    (c : K) (u : Fin n → ℂ → ℂ)
    (hu : ∀ i, AnalyticAt ℂ (u i) (φ c)) (hind : v5FiniteGermIndependent (φ c) u)
    (hode : ∀ i, ∀ᶠ z in 𝓝 (φ c),
      v5RowResidual (u i) n (fun j => (p j).map φ) z = 0)
    (hzero : ∀ i, u i (φ c) = 0) (f : ℂ → ℂ)
    (hf : AnalyticAt ℂ f (ψ c))
    (hfode : ∀ᶠ z in 𝓝 (ψ c), v5RowResidual f n (fun j => (p j).map ψ) z = 0) :
    f (ψ c) = 0 := by
  let g := fun z : ℂ => f (z+ψ c)
  let P := fun j => (p j).map ψ
  let q := v5ShiftPolynomialRow P (ψ c)
  have ht : Tendsto (fun z : ℂ => z+ψ c) (𝓝 0) (𝓝 (ψ c)) := by
    simpa [ContinuousAt] using (continuousAt_id (x := (0:ℂ))).add continuousAt_const
      (g := fun _ => ψ c)
  have hgo : ∀ᶠ z in 𝓝 (0:ℂ), v5RowResidual g n q z = 0 := by
    filter_upwards [ht.eventually hfode] with z hz
    exact (v5_shift_row_residual P n f (ψ c) z).trans hz
  obtain ⟨y,hy⟩ := analyticAt_has_ordinary_series g (v5_shift_analyticAt hf)
  have hyode := v5_formal_ode_from_analytic_germ q g y hy hgo
  have hy0 := v5_formal_scalar_zero_under_alternate_embedding hn φ ψ p hp c u hu hind hode hzero
    y hyode
  simpa only [v5_series_coeff_zero_of_realized g y hy,g,zero_add] using hy0

/-- For a nonzero rational-coefficient broad E-function vanishing at 1,
every formal local solution at 1 of its minimal equation vanishes there,
not just the constructed independent analytic family. -/
theorem v5_rational_broad_all_formal_solutions_zero_at_one
    (f : ℂ → ℂ) (a : ℕ → AlgebraicComplex)
    (hf : Differentiable ℂ f)
    (hs : ∀ z : ℂ, HasSum (fun n => (a n : ℂ)*z^n/(n.factorial : ℂ)) (f z))
    (hODE : HasAlgebraicPolynomialODE f) (ha : V5BroadAlgebraicArithmetic a)
    (hrat : ∀ n, ∃ q : ℚ, a n = algebraMap ℚ AlgebraicComplex q)
    (hzero : f 1 = 0) (hf0 : f ≠ 0)
    (m : ℕ) (hm : 0 < m) (p : ℕ → Polynomial AlgebraicComplex) (hp : p m ≠ 0)
    (hp0 : ∀ z, v5RowResidual f m p z = 0)
    (hmin : ∀ l < m, ¬ v5HasAnnihilatorOrder AlgebraicComplex f l)
    (y : PowerSeries ℂ)
    (hy : v5ScalarODE (v5ShiftPolynomialRow
      (fun j => (p j).map (algebraMap AlgebraicComplex ℂ)) 1) (m+1) y = 0) :
    PowerSeries.coeff ℂ 0 y = 0 := by
  obtain ⟨u,hi,hu⟩ := v5_broad_rational_minimal_row_vanishing_at_one f a hf hs hODE ha
    hrat hzero hf0 m p hp hp0 hmin
  let φ : AlgebraicComplex →+* ℂ := algebraMap AlgebraicComplex ℂ
  apply v5_formal_scalar_zero_of_vanishing_analytic_family hm (fun j => (p j).map φ)
    ((Polynomial.map_ne_zero_iff φ.injective).mpr hp) u 1 (fun i => (hu i).1) hi
    ?_ (fun i => (hu i).2.1) y hy
  intro i
  filter_upwards [(hu i).2.2] with z hz
  change (∑ j ∈ Finset.range (m+1), ((p j).map φ).eval z * iteratedDeriv j (u i) z) = 0
  simpa only [Polynomial.eval_map] using hz

#print axioms v5_rational_broad_all_formal_solutions_zero_at_one
#print axioms v5_formal_scalar_zero_of_vanishing_analytic_family
#print axioms v5_formal_scalar_zero_under_alternate_embedding
#print axioms v5_analytic_scalar_zero_under_alternate_embedding
end StrictEUnit
end
