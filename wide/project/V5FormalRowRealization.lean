import EntireTaylorEmbedding
import V5PolynomialRowComposition

namespace StrictEUnit
open scoped Topology BigOperators

noncomputable def v5FormalRow (p : ℕ → Polynomial ℂ) (m : ℕ)
    (F : PowerSeries ℂ) : PowerSeries ℂ :=
  ∑ k ∈ Finset.range (m+1), (p k : PowerSeries ℂ) *
    (PowerSeries.derivative ℂ : PowerSeries ℂ → PowerSeries ℂ)^[k] F

theorem v5_entireTaylor_iterate (f : entireFunctionAlgebra) (k : ℕ) :
    entireTaylorAlgHom ((entireFunctionDerivative)^[k] f) =
      (PowerSeries.derivative ℂ : PowerSeries ℂ → PowerSeries ℂ)^[k]
        (entireTaylorAlgHom f) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      entireTaylorAlgHom_derivative, ih]

theorem v5_entireFunction_iterate_apply (f : entireFunctionAlgebra) (k : ℕ) (z : ℂ) :
    ((entireFunctionDerivative)^[k] f).val z = iteratedDeriv k f.val z := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', iteratedDeriv_succ]
    change deriv (((entireFunctionDerivative)^[k] f).val) z = _
    congr 1
    funext w
    exact ih w

/-- Formal scalar polynomial equations for a genuine entire Taylor image are
equivalent to actual equations on the whole complex plane. -/
theorem v5_formalRow_eq_zero_iff (f : entireFunctionAlgebra)
    (p : ℕ → Polynomial ℂ) (m : ℕ) :
    v5FormalRow p m (entireTaylorAlgHom f) = 0 ↔
      ∀ z, v5RowResidual f.val m p z = 0 := by
  let g : entireFunctionAlgebra := ∑ k ∈ Finset.range (m+1),
    polynomialEntireAlgHom (p k) * (entireFunctionDerivative)^[k] f
  have ht : entireTaylorAlgHom g = v5FormalRow p m (entireTaylorAlgHom f) := by
    simp only [g, map_sum, map_mul, entireTaylorAlgHom_polynomial,
      v5_entireTaylor_iterate, v5FormalRow]
  have hg (z : ℂ) : g.val z = v5RowResidual f.val m p z := by
    change entireEvaluation z g = _
    simp only [g, map_sum, map_mul, entireEvaluation_apply,
      polynomialEntireAlgHom_apply, v5_entireFunction_iterate_apply]
    rfl
  constructor
  · intro h z
    have h0 : g = 0 := entireTaylorAlgHom_injective (by rw [ht, h, map_zero])
    rw [← hg, h0]
    rfl
  · intro h
    have h0 : g = 0 := by
      apply Subtype.ext
      funext z
      exact (hg z).trans (h z)
    rw [← ht, h0, map_zero]

/-- Specifying all factorial-normalized Taylor coefficients identifies the
formal series uniquely, without evaluating any arbitrary formal series. -/
theorem v5_formalRow_realization {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (F : PowerSeries ℂ)
    (hF : ∀ k, PowerSeries.coeff ℂ k F = iteratedDeriv k f 0 / (k.factorial : ℂ))
    (p : ℕ → Polynomial ℂ) (m : ℕ)
    (hode : v5FormalRow p m F = 0) :
    ∀ z, v5RowResidual f m p z = 0 := by
  have he : F = entireFormalTaylor f := by
    ext k
    rw [hF, coeff_entireFormalTaylor]
    have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    apply (div_eq_iff hk).2
    simpa only [mul_comm] using (entireCauchyCoefficient_factorial hf k).symm
  apply (v5_formalRow_eq_zero_iff ⟨f, hf⟩ p m).mp
  simpa only [entireTaylorAlgHom_apply, he] using hode

#print axioms v5_entireTaylor_iterate
#print axioms v5_entireFunction_iterate_apply
#print axioms v5_formalRow_eq_zero_iff
#print axioms v5_formalRow_realization
end StrictEUnit
