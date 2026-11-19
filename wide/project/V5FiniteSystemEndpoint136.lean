import V5WideValueClassificationBoundary131
import V5ActualWideReciprocalFiber
noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- A classification proved on literal finite Laurent systems finishes the
normalized wide theorem. The sum indexing creates no additional assumption. -/
theorem v5_wide_reciprocal_of_finite_system136
    (hfinish : ∀ (r : ℕ) (F : Fin r → entireFunctionAlgebra)
      (A : Matrix (Fin r) (Fin r) (LaurentPolynomial AlgebraicComplex)),
      (∀ i, V5IsBroadEFunction (F i).val) →
      (∀ z : ℂˣ, ∀ i, deriv (F i).val (z : ℂ) =
        ∑ j, arithmeticLaurentEvaluation z (A i j) * (F j).val (z : ℂ)) →
      ∀ i j, (F i).val 1 * (F j).val 1 = 1 →
      ∃ α β : AlgebraicComplex, α ≠ 0 ∧
        (F i).val 1 = (α : ℂ) * Complex.exp (β : ℂ)) :
    V5WideReciprocalAtOne131 := by
  intro f g hf hg hfg
  obtain ⟨n,m,F,A,i,j,hi,hj,hF,hA,_⟩ :=
    v5_actual_wide_reciprocal_exact_fiber hf hg hfg
  let e : Fin n ⊕ Fin m ≃ Fin (n+m) := finSumFinEquiv
  let G : Fin (n+m) → entireFunctionAlgebra := fun a => F (e.symm a)
  let B : Matrix (Fin (n+m)) (Fin (n+m)) (LaurentPolynomial AlgebraicComplex) :=
    fun a b => A (e.symm a) (e.symm b)
  have hG : ∀ a, V5IsBroadEFunction (G a).val := fun a => hF (e.symm a)
  have hB : ∀ z : ℂˣ, ∀ a, deriv (G a).val (z : ℂ) =
      ∑ b, arithmeticLaurentEvaluation z (B a b) * (G b).val (z : ℂ) := by
    intro z a
    rw [show (G a).val = (F (e.symm a)).val from rfl, hA]
    exact (Equiv.sum_comp e.symm
      (fun b => arithmeticLaurentEvaluation z (A (e.symm a) b) * (F b).val (z : ℂ))).symm
  have hGi : (G (e i)).val = f := by simpa only [G, e.symm_apply_apply] using hi
  have hGj : (G (e j)).val = g := by simpa only [G, e.symm_apply_apply] using hj
  have hr : (G (e i)).val 1 * (G (e j)).val 1 = 1 := by rw [hGi,hGj]; exact hfg
  simpa only [hGi] using hfinish (n+m) G B hG hB (e i) (e j) hr
end StrictEUnit
#print axioms StrictEUnit.v5_wide_reciprocal_of_finite_system136
