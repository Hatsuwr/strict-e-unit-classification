import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! New reconstruction of the elementary specialized-span lifting interface
used by the unchanged ordinary relation/cyclic dichotomy. Scalar combinations
of specialized polynomial relation rows lift using constant polynomials. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators
namespace StrictEUnit

/-- Every vector in the span of the specialized relation basis is the literal
specialization of a polynomial row in the original relation kernel. -/
theorem polynomial_relation_of_specialized_span
    {K N ι κ : Type*} [Field K] [AddCommGroup N]
    [Module (Polynomial K) N] [Fintype ι] [Fintype κ]
    (F : (ι → Polynomial K) →ₗ[Polynomial K] N)
    (B : Basis κ (Polynomial K) (LinearMap.ker F))
    (α : K) (c : ι → K)
    (hc : c ∈ Submodule.span K (Set.range (fun i j => ((B i).val j).eval α))) :
    ∃ p : ι → Polynomial K, p ∈ LinearMap.ker F ∧ ∀ j, (p j).eval α = c j := by
  classical
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hc
  let p : ι → Polynomial K := ∑ i, Polynomial.C (a i) • (B i).val
  refine ⟨p, ?_, ?_⟩
  · apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem (LinearMap.ker F) (Polynomial.C (a i)) (B i).property
  · intro j
    calc
      (p j).eval α = ∑ i, a i * ((B i).val j).eval α := by
        simp only [p, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C]
      _ = c j := by
        simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun ha j

end StrictEUnit
