import V5ActualWideLaurentSystem
import V5WideSolutionFiber

noncomputable section
set_option maxHeartbeats 4200000
set_option synthInstance.maxHeartbeats 160000
open scoped BigOperators
namespace StrictEUnit

/-- Literal numerical reciprocal values lie in the exact fiber of a
common finite Laurent solution algebra and are represented by inverse
elements there. No functional inverse is claimed before descent. -/
theorem v5_actual_wide_reciprocal_exact_fiber {f g : ℂ → ℂ}
    (hf : V5IsBroadEFunction f) (hg : V5IsBroadEFunction g)
    (hfg : f 1 * g 1 = 1) :
    ∃ n m : ℕ, ∃ F : (Fin n ⊕ Fin m) → entireFunctionAlgebra,
      ∃ A : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) (LaurentPolynomial AlgebraicComplex),
      ∃ i j : (Fin n ⊕ Fin m),
        (F i).val = f ∧ (F j).val = g ∧
        (∀ u, V5IsBroadEFunction (F u).val) ∧
        (∀ (z : ℂˣ) u, deriv (F u).val (z : ℂ) =
          ∑ v, arithmeticLaurentEvaluation z (A u v) * (F v).val (z : ℂ)) ∧
        RingHom.ker (v5WideSolutionEvaluation F).toRingHom = v5WideSolutionIdeal F ∧
        ∃ u : (v5WideSolutionAlgebra F ⧸ v5WideSolutionIdeal F)ˣ,
          u.val = Ideal.Quotient.mk (v5WideSolutionIdeal F) (v5WideSolutionEntry F i) ∧
          u.inv = Ideal.Quotient.mk (v5WideSolutionIdeal F) (v5WideSolutionEntry F j) := by
  classical
  have hfn : f ≠ 0 := by
    intro he
    simp [he] at hfg
  have hgn : g ≠ 0 := by
    intro he
    simp [he] at hfg
  obtain ⟨n,m,F,A,i,j,hi,hj,hFw,hFA⟩ :=
    v5_actual_wide_common_laurent_system hf hg hfn hgn
  have hK := v5WideSolution_exact_kernel F A hFw hFA
  let I := v5WideSolutionIdeal F
  let u := Ideal.Quotient.mk I (v5WideSolutionEntry F i)
  let v := Ideal.Quotient.mk I (v5WideSolutionEntry F j)
  have he : v5WideSolutionEntry F i * v5WideSolutionEntry F j - 1 ∈ I := by
    change _ ∈ v5WideSolutionIdeal F
    rw [← hK]
    change (F i).val 1 * (F j).val 1 - 1 = 0
    rw [hi,hj,hfg,sub_self]
  have hv : u * v = 1 := by
    let π : v5WideSolutionAlgebra F →+* (v5WideSolutionAlgebra F ⧸ I) :=
      Ideal.Quotient.mk I
    have h : π (v5WideSolutionEntry F i * v5WideSolutionEntry F j - 1) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem (I := I)).mpr he
    exact sub_eq_zero.mp (by simpa only [map_sub,map_mul,map_one] using h)
  let w : (v5WideSolutionAlgebra F ⧸ I)ˣ := ⟨u,v,hv,by rw [mul_comm v u]; exact hv⟩
  exact ⟨n,m,F,A,i,j,hi,hj,hFw,hFA,hK,w,rfl,rfl⟩

#print axioms v5_actual_wide_reciprocal_exact_fiber
end StrictEUnit
