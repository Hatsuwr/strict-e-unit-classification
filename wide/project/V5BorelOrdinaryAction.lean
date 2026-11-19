import V5BorelOrdinaryAdapter

namespace StrictEUnit
open scoped Topology BigOperators

theorem v5_eulerPolynomialRow_action (j : ℕ) (f : ℂ → ℂ) :
    v5RowResidual f j (v5EulerPolynomialRow j) =
      fun z => z^j * iteratedDeriv j f z := by
  funext z
  unfold v5RowResidual v5EulerPolynomialRow
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    simp [hkj]
  · simp

theorem v5_iteratePolynomialRow_action (a : ℕ → Polynomial ℂ) (m k : ℕ)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ) :
    v5RowResidual f (m+k) (v5IteratePolynomialRow a m k) z =
      iteratedDeriv k (v5RowResidual f m a) z := by
  have ha : ∀ j, AnalyticOnNhd ℂ (v5EvalPolynomialRow a j) Set.univ := by
    intro j w _
    simpa only [v5EvalPolynomialRow, Polynomial.aeval_def] using
      (analyticAt_id : AnalyticAt ℂ (fun z : ℂ => z) w).aeval_polynomial (a j)
  have h := v5_iteratedDeriv_functionRow isOpen_univ ha
    (fun w _ => hf.analyticAt w) m k z (Set.mem_univ z)
  rw [← v5_evalPolynomialRow_iterate] at h
  exact h.symm

/-- The explicit polynomial row acts as the finite differentiated Euler sum. -/
theorem v5_borelPolynomialRow_action {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (p j : ι → ℕ) (P m : ℕ) (hj : ∀ i, j i ≤ m)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ) :
    v5RowResidual f (P+m) (v5BorelPolynomialRow c p j P) z =
      ∑ i, c i * iteratedDeriv (P-p i) (fun w => w^(j i) * iteratedDeriv (j i) f w) z := by
  classical
  have hC (v : ℂ) : (Polynomial.eval₂RingHom (algebraMap ℂ ℂ) z) (Polynomial.C v) = v := by simp
  unfold v5RowResidual v5BorelPolynomialRow
  simp only [map_sum, map_mul, hC,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_assoc, ← Finset.mul_sum]
  congr 1
  change v5FunctionRow
    (v5EvalPolynomialRow (v5TruncatePolynomialRow
      (v5IteratePolynomialRow (v5EulerPolynomialRow (j i)) (j i) (P-p i))
      (j i+(P-p i)))) (P+m) f z = _
  rw [v5_evalPolynomialRow_truncate,
    v5_truncateRow_padding _ (show j i+(P-p i) ≤ P+m by have := hj i; omega)]
  change v5RowResidual f (j i+(P-p i))
    (v5IteratePolynomialRow (v5EulerPolynomialRow (j i)) (j i) (P-p i)) z = _
  rw [v5_iteratePolynomialRow_action _ _ _ hf, v5_eulerPolynomialRow_action]

noncomputable def v5EntireEulerFalling (j : ℕ) (f : entireFunctionAlgebra) :
    entireFunctionAlgebra :=
  polynomialEntireAlgHom (Polynomial.X^j) * (entireFunctionDerivative)^[j] f

theorem v5_entireEulerFalling_apply (j : ℕ) (f : entireFunctionAlgebra) (z : ℂ) :
    (v5EntireEulerFalling j f).val z = z^j * iteratedDeriv j f.val z := by
  change (polynomialEntireAlgHom (Polynomial.X^j)).val z *
    ((entireFunctionDerivative)^[j] f).val z = _
  rw [polynomialEntireAlgHom_apply, v5_entireFunction_iterate_apply]
  simp

theorem v5_entireTaylor_eulerFalling (j : ℕ) (f : entireFunctionAlgebra) :
    entireTaylorAlgHom (v5EntireEulerFalling j f) =
      v5EulerFalling j (entireTaylorAlgHom f) := by
  simp only [v5EntireEulerFalling, map_mul, entireTaylorAlgHom_polynomial,
    v5_entireTaylor_iterate, Polynomial.coe_pow, Polynomial.coe_X, v5EulerFalling]

/-- A finite Borel identity for the factorial coefficients of an actual entire
function gives global annihilation by the explicitly constructed polynomial row. -/
theorem v5_borelPolynomialRow_annihilates {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (p j : ι → ℕ) (P m : ℕ)
    (hj : ∀ i, j i ≤ m) (hp : ∀ i, p i ≤ P)
    (f : entireFunctionAlgebra) (B : PowerSeries ℂ)
    (hBF : ∀ n, PowerSeries.coeff ℂ n B = v5FactorialCoeff (entireTaylorAlgHom f) n)
    (hB : ∑ i, PowerSeries.C ℂ (c i) *
      (PowerSeries.X^p i * v5EulerFalling (j i) B) = 0) :
    ∀ z, v5RowResidual f.val (P+m) (v5BorelPolynomialRow c p j P) z = 0 := by
  classical
  let g : entireFunctionAlgebra := ∑ i,
    algebraMap ℂ entireFunctionAlgebra (c i) *
      (entireFunctionDerivative)^[P-p i] (v5EntireEulerFalling (j i) f)
  have hg : entireTaylorAlgHom g = 0 := by
    simp only [g, map_sum, map_mul, AlgHom.commutes, PowerSeries.algebraMap_eq,
      v5_entireTaylor_iterate, v5_entireTaylor_eulerFalling]
    exact v5_borel_finite_equation_transfer c p j P hp hBF hB
  have hg0 : g = 0 := entireTaylorAlgHom_injective (hg.trans (map_zero _).symm)
  intro z
  rw [v5_borelPolynomialRow_action c p j P m hj f.property]
  have he := congrArg (entireEvaluation z) hg0
  simp only [g, map_sum, map_mul, AlgHom.commutes, entireEvaluation_apply,
    v5_entireFunction_iterate_apply, map_zero] at he
  have hfunc (i : ι) : (v5EntireEulerFalling (j i) f).val =
      fun w => w^(j i) * iteratedDeriv (j i) f.val w := by
    funext w
    exact v5_entireEulerFalling_apply _ _ _
  simpa only [hfunc] using he

/-- Under the finite Fuchs support conditions the constructed, positive-order
annihilator is ordinary at every nonzero complex point. -/
theorem v5_borel_ordinary_annihilator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ℂ) (p j : ι → ℕ) (P m : ℕ) (i₀ : ι)
    (hj : ∀ i, j i ≤ m) (hp : ∀ i, p i ≤ P)
    (hj₀ : j i₀ = m) (hp₀ : p i₀ = 0)
    (hunique : ∀ i, i ≠ i₀ → j i < m ∨ 0 < p i)
    (hc : c i₀ ≠ 0) (horder : 0 < P+m)
    (f : entireFunctionAlgebra) (B : PowerSeries ℂ)
    (hBF : ∀ n, PowerSeries.coeff ℂ n B = v5FactorialCoeff (entireTaylorAlgHom f) n)
    (hB : ∑ i, PowerSeries.C ℂ (c i) *
      (PowerSeries.X^p i * v5EulerFalling (j i) B) = 0) :
    ∃ (n : ℕ) (a : ℕ → Polynomial ℂ), 0 < n ∧
      (∀ z, v5RowResidual f.val n a z = 0) ∧
      ∀ z : ℂ, z ≠ 0 → (a n).eval z ≠ 0 :=
  ⟨P+m, v5BorelPolynomialRow c p j P, horder,
    v5_borelPolynomialRow_annihilates c p j P m hj hp f B hBF hB,
    fun _ hz => v5_borelPolynomialRow_ordinary c p j P m i₀ hj hp hj₀ hp₀ hunique hc hz⟩

#print axioms v5_borelPolynomialRow_action
#print axioms v5_borelPolynomialRow_annihilates
#print axioms v5_borel_ordinary_annihilator
end StrictEUnit
