import V5ActualLaurentCompanion
import V5ActualWideDerivative
import V5OrdinaryLeadingMonomial

noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- Every nonzero actual wide E-function occurs literally as the zeroth
coordinate of a finite wide Laurent first-order system. -/
theorem v5_actual_wide_laurent_derivative_system {f : ℂ → ℂ}
    (hf : V5IsBroadEFunction f) (hne : f ≠ 0) :
    ∃ n : ℕ, 0 < n ∧
      ∃ F : Fin n → entireFunctionAlgebra,
      ∃ A : Matrix (Fin n) (Fin n) (LaurentPolynomial AlgebraicComplex),
        (∀ i, V5IsBroadEFunction (F i).val) ∧
        (∀ i, (F i).val = iteratedDeriv i.val f) ∧
        ∀ (z : ℂˣ) i, deriv (F i).val (z : ℂ) =
          ∑ j, arithmeticLaurentEvaluation z (A i j) * (F j).val (z : ℂ) := by
  obtain ⟨n,p,hn,hrow,hp⟩ := v5_actual_broad_annihilator_over_algebraic hf hne
  obtain ⟨L,hL⟩ := v5_polynomial_only_origin_laurent_inverse (p n) hp
  let hw (i : Fin n) := v5_broad_actual_iteratedDeriv i.val hf
  let F : Fin n → entireFunctionAlgebra := fun i => ⟨iteratedDeriv i.val f,(hw i).choose_spec.1⟩
  exact ⟨n,hn,F,v5ActualLaurentCompanionMatrix n p L,hw,fun _ => rfl,
    v5_actual_laurent_companion_rows f n p hrow L hL⟩

/-- Two nonzero wide functions share one actual Laurent system, retaining
them as literal coordinates, without a determinant or a strict frame. -/
theorem v5_actual_wide_common_laurent_system {f g : ℂ → ℂ}
    (hf : V5IsBroadEFunction f) (hg : V5IsBroadEFunction g) (hfn : f ≠ 0) (hgn : g ≠ 0) :
    ∃ n m : ℕ, ∃ F : (Fin n ⊕ Fin m) → entireFunctionAlgebra,
      ∃ A : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) (LaurentPolynomial AlgebraicComplex),
      ∃ i j : (Fin n ⊕ Fin m),
        (F i).val = f ∧ (F j).val = g ∧
        (∀ u, V5IsBroadEFunction (F u).val) ∧
        ∀ (z : ℂˣ) u, deriv (F u).val (z : ℂ) =
          ∑ v, arithmeticLaurentEvaluation z (A u v) * (F v).val (z : ℂ) := by
  obtain ⟨n,hn,F,A,hFw,hFval,hF⟩ := v5_actual_wide_laurent_derivative_system hf hfn
  obtain ⟨m,hm,G,B,hGw,hGval,hG⟩ := v5_actual_wide_laurent_derivative_system hg hgn
  let i : Fin n := ⟨0,hn⟩
  let j : Fin m := ⟨0,hm⟩
  refine ⟨n,m,Sum.elim F G,Matrix.fromBlocks A 0 0 B,Sum.inl i,Sum.inr j,?_,?_,?_,?_⟩
  · simpa only [Sum.elim_inl,i,iteratedDeriv_zero] using hFval i
  · simpa only [Sum.elim_inr,j,iteratedDeriv_zero] using hGval j
  · intro u
    cases u with
    | inl u => exact hFw u
    | inr u => exact hGw u
  · exact v5_actual_laurent_sum_system F G A B hF hG

#print axioms v5_actual_wide_laurent_derivative_system
#print axioms v5_actual_wide_common_laurent_system
end StrictEUnit
