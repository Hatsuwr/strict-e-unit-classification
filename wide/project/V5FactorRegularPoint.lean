import V5FactorFamilyAssembly

namespace StrictEUnit
open scoped Topology BigOperators
open Filter

/-- Every neighborhood contains a point avoiding all the given exceptional
polynomials. The neighborhood need not be open, nor the center regular. -/
theorem v5_exists_auxiliary_regular_point {ι : Type*} [Fintype ι]
    (p : ι → Polynomial ℂ) (hp : ∀ i, p i ≠ 0)
    {D : Set ℂ} {x : ℂ} (hD : D ∈ 𝓝 x) :
    ∃ y ∈ D, ∀ i, (p i).eval y ≠ 0 := by
  classical
  let P := ∏ i, p i
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hp i
  obtain ⟨y, hP_y, hy⟩ := (v5_dense_polynomial_eval_ne_zero P hP).inter_nhds_nonempty hD
  refine ⟨y, hy, ?_⟩
  have hn : P.eval y ≠ 0 := by simpa using hP_y
  unfold P at hn
  rw [Polynomial.eval_prod] at hn
  exact fun i => Finset.prod_ne_zero_iff.mp hn i (Finset.mem_univ i)

private theorem v5_eval_polynomial_analyticAt (p : Polynomial ℂ) (x : ℂ) :
    AnalyticAt ℂ (fun z => p.eval z) x := by
  simpa only [Polynomial.aeval_def] using
    (analyticAt_id : AnalyticAt ℂ (fun z : ℂ => z) x).aeval_polynomial p

/-- The factor-family extraction can take a pointwise left-action identity
away from a nonzero exceptional polynomial. Existence of the regular
auxiliary point and of a neighborhood there are consequences, not premises. -/
theorem v5_extract_right_factor_family_off_exceptional {K L : Type*}
    [Field K] [Algebra K ℂ] [Field L] [Algebra L ℂ]
    {n m : ℕ} (hm : m ≤ n) {x : ℂ} {D : Set ℂ}
    (hopen : IsOpen D) (hD : IsPreconnected D) (hx : x ∈ D)
    (u : Fin n → ℂ → ℂ) (hu : ∀ j, AnalyticOnNhd ℂ (u j) D)
    (hind : v5FiniteGermIndependent x u)
    (q : ℕ → Polynomial K) (d e : Polynomial ℂ) (hd : d ≠ 0) (he : e ≠ 0)
    (r : ℕ → Polynomial L) (hr : r (n-m) ≠ 0)
    (hleft : ∀ j z, z ∈ D → d.eval z ≠ 0 → e.eval z ≠ 0 →
      v5RowResidual (fun w => v5RowResidual (u j) m q w / d.eval w) (n-m) r z = 0) :
    ∃ v : Fin m → ℂ → ℂ, v5FiniteGermIndependent x v ∧
      ∀ i, AnalyticOnNhd ℂ (v i) D ∧ ∀ᶠ z in 𝓝 x, v5RowResidual (v i) m q z = 0 := by
  let R := (r (n-m)).map (algebraMap L ℂ)
  have hR : R ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap L ℂ).injective).2 hr
  have hP : d * e * R ≠ 0 := mul_ne_zero (mul_ne_zero hd he) hR
  have hDx := hopen.mem_nhds hx
  obtain ⟨y, hPy, hy⟩ := (v5_dense_polynomial_eval_ne_zero (d * e * R) hP).inter_nhds_nonempty hDx
  have hne : d.eval y * e.eval y * R.eval y ≠ 0 := by
    simpa [Polynomial.eval_mul] using hPy
  have hdy : d.eval y ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hne).1).1
  have hey : e.eval y ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hne).1).2
  have hry : (r (n-m)).eval₂ (algebraMap L ℂ) y ≠ 0 := by
    simpa only [R, Polynomial.eval_map] using (mul_ne_zero_iff.mp hne).2
  apply v5_extract_right_factor_family hm hD hDx hy u hu hind q
    (fun z => d.eval z) (v5_eval_polynomial_analyticAt d y) hdy r hry
  intro j
  have hD' : ∀ᶠ z in 𝓝 y, z ∈ D := hopen.mem_nhds hy
  have hd' : ∀ᶠ z in 𝓝 y, d.eval z ≠ 0 :=
    (v5_eval_polynomial_analyticAt d y).continuousAt.eventually_ne hdy
  have he' : ∀ᶠ z in 𝓝 y, e.eval z ≠ 0 :=
    (v5_eval_polynomial_analyticAt e y).continuousAt.eventually_ne hey
  filter_upwards [hD', hd', he'] with z hz hdz hez
  exact hleft j z hz hdz hez

#print axioms v5_exists_auxiliary_regular_point
#print axioms v5_extract_right_factor_family_off_exceptional
end StrictEUnit
