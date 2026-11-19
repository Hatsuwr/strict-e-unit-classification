import V5LaurentMatrixODE
import V5FormalBaseTaylor
import V5EntireLogTaylor
import Mathlib.Analysis.Analytic.Constructions

noncomputable section
open scoped Matrix.L2OpNorm Topology
namespace StrictEUnit

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem v5_hasDerivAt_matrix_entry {f : ℂ → Matrix ι ι ℂ} {y : Matrix ι ι ℂ}
    {z : ℂ} (h : HasDerivAt f y z) (i j : ι) :
    HasDerivAt (fun w => f w i j) (y i j) z := by
  let L : Matrix ι ι ℂ →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)
  change HasDerivAt (L ∘ f) (L y) z
  exact L.hasFDerivAt.comp_hasDerivAt z h

/-- An analytic matrix function satisfying a local differential system gives an
entrywise formal Taylor solution of the same system. -/
theorem v5_local_taylor_matrix_ode {c : ℂ} (A F : ℂ → Matrix ι ι ℂ)
    (hA : ∀ i j, AnalyticAt ℂ (fun z => A z i j) c)
    (hF : ∀ i j, AnalyticAt ℂ (fun z => F z i j) c)
    (hode : ∀ᶠ z in 𝓝 c, HasDerivAt F (A z * F z) z) :
    (Matrix.of (fun i j => v5LocalTaylor (fun z => F z i j) c)).map
      (PowerSeries.derivative ℂ) =
      Matrix.of (fun i j => v5LocalTaylor (fun z => A z i j) c) *
        Matrix.of (fun i j => v5LocalTaylor (fun z => F z i j) c) := by
  apply Matrix.ext
  intro i j
  let q (k : ι) : v5LocalAnalyticAlgebra c :=
    (⟨fun z => A z i k, hA i k⟩ : v5LocalAnalyticAlgebra c) *
      ⟨fun z => F z k j, hF k j⟩
  let p : v5LocalAnalyticAlgebra c := ∑ k, q k
  have hp (z : ℂ) : p.val z = (A z * F z) i j := by
    change ((v5LocalAnalyticAlgebra c).val (∑ k, q k)) z = _
    rw [map_sum (v5LocalAnalyticAlgebra c).val]
    simp only [Finset.sum_apply, Matrix.mul_apply]
    rfl
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply]
  rw [← v5LocalTaylor_deriv]
  calc
    v5LocalTaylor (deriv (fun z => F z i j)) c = v5LocalTaylor p.val c := by
      apply (v5LocalTaylor_eq_iff_eventuallyEq (hF i j).deriv p.property).mpr
      filter_upwards [hode] with z hz
      rw [(v5_hasDerivAt_matrix_entry hz i j).deriv, hp]
    _ = ∑ k, v5LocalTaylor (fun z => A z i k) c *
        v5LocalTaylor (fun z => F z k j) c := by
      change (v5LocalTaylorAlgHom c) (∑ k, q k) = _
      rw [map_sum]
      exact Finset.sum_congr rfl (fun k _ => map_mul (v5LocalTaylorAlgHom c) _ _)

omit [Fintype ι] [DecidableEq ι] in
/-- Taylor series of the literal Laurent matrix evaluation agrees entrywise
with the coefficient-field base change of the pointed Laurent algebra. -/
theorem v5_eval_laurent_matrix_taylor {K : Type*} [Field K] (f : K →+* ℂ)
    (A : Matrix ι ι (LaurentPolynomial K)) (i j : ι) :
    AnalyticAt ℂ (fun z => v5EvalLaurentMatrix f A z i j) 1 ∧
      v5LocalTaylor (fun z => v5EvalLaurentMatrix f A z i j) 1 =
        PowerSeries.map f (v5WidePointedBase K (A i j)) := by
  have h : (v5LocalLaurentEval f (A i j)).val =ᶠ[𝓝 (1 : ℂ)]
      (fun z => v5EvalLaurentMatrix f A z i j) := by
    filter_upwards [isOpen_ne.mem_nhds (one_ne_zero : (1 : ℂ) ≠ 0)] with z hz
    simpa only [v5EvalLaurentMatrix, dif_neg hz] using
      v5LocalLaurentEval_apply f (A i j) z hz
  have ha := (v5LocalLaurentEval f (A i j)).property
  refine ⟨ha.congr h, ?_⟩
  rw [(v5LocalTaylor_eq_iff_eventuallyEq (ha.congr h) ha).mpr h.symm]
  exact v5LocalLaurentEval_taylor f (A i j)

/-- The analytic fundamental matrix and an entire reciprocal determinant realize
the normalized formal system at 1, over the actual embedded coefficient field. -/
theorem v5_laurent_matrix_ode_taylor {K : Type*} [Field K] (f : K →+* ℂ)
    (A : Matrix ι ι (LaurentPolynomial K)) :
    ∃ (U : ℂ → Matrix ι ι ℂ) (v : ℂ → ℂ),
      let W := Matrix.of (fun i j => v5LocalTaylor (fun z => U (Complex.log z) i j) 1)
      Differentiable ℂ U ∧ Differentiable ℂ v ∧ (∀ w, v w * (U w).det = 1) ∧
        W.map (PowerSeries.constantCoeff ℂ) = 1 ∧
        W.map (PowerSeries.derivative ℂ) =
          (A.map (fun p => PowerSeries.map f (v5WidePointedBase K p))) * W := by
  obtain ⟨U, v, h0, hU, hv, hinv, hode⟩ := v5_laurent_matrix_ode_marked_entire f A
  refine ⟨U, v, hU, hv, hinv, ?_, ?_⟩
  · apply Matrix.ext
    intro i j
    simp only [Matrix.map_apply, Matrix.of_apply, v5LocalTaylor_constantCoeff, h0]
  · have hF (i j : ι) : AnalyticAt ℂ (fun z => U (Complex.log z) i j) 1 :=
      ((v5_matrix_entry_differentiable hU i j).analyticAt _).comp v5_log_analyticAt_one
    have hW := v5_local_taylor_matrix_ode (v5EvalLaurentMatrix f A)
      (fun z => U (Complex.log z)) (fun i j => (v5_eval_laurent_matrix_taylor f A i j).1) hF hode
    have hbase : Matrix.of (fun i j => v5LocalTaylor (fun z => v5EvalLaurentMatrix f A z i j) 1) =
        A.map (fun p => PowerSeries.map f (v5WidePointedBase K p)) := by
      apply Matrix.ext
      intro i j
      exact (v5_eval_laurent_matrix_taylor f A i j).2
    simpa only [hbase] using hW

end StrictEUnit
#print axioms StrictEUnit.v5_hasDerivAt_matrix_entry
#print axioms StrictEUnit.v5_local_taylor_matrix_ode
#print axioms StrictEUnit.v5_eval_laurent_matrix_taylor
#print axioms StrictEUnit.v5_laurent_matrix_ode_taylor
