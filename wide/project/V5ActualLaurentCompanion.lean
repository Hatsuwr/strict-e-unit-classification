import V5BroadActualRegularity
import Stage20ArithmeticFrameLifting
import Mathlib.Data.Matrix.Block

noncomputable section
set_option maxHeartbeats 2400000
open scoped BigOperators
namespace StrictEUnit

def v5ActualLaurentCompanionMatrix (n : ℕ) (p : ℕ → Polynomial AlgebraicComplex)
    (L : LaurentPolynomial AlgebraicComplex) :
    Matrix (Fin n) (Fin n) (LaurentPolynomial AlgebraicComplex) :=
  fun i j => if i.val+1 < n then if j.val = i.val+1 then 1 else 0
    else -(L * Polynomial.toLaurent (p j.val))

/-- The prefix of actual derivatives satisfies the literal normalized Laurent
companion equations whenever the leading polynomial has a Laurent inverse. -/
theorem v5_actual_laurent_companion_rows
    (f : ℂ → ℂ) (n : ℕ) (p : ℕ → Polynomial AlgebraicComplex)
    (hrow : ∀ z, v5RowResidual f n p z = 0)
    (L : LaurentPolynomial AlgebraicComplex)
    (hL : ∀ z : ℂˣ, arithmeticLaurentEvaluation z L *
      (p n).eval₂ (algebraicClosure ℚ ℂ).val.toRingHom (z : ℂ) = 1) :
    ∀ (z : ℂˣ) (i : Fin n), deriv (iteratedDeriv i.val f) (z : ℂ) =
      ∑ j, arithmeticLaurentEvaluation z (v5ActualLaurentCompanionMatrix n p L i j) *
        iteratedDeriv j.val f (z : ℂ) := by
  classical
  intro z i
  rw [← iteratedDeriv_succ]
  by_cases hi : i.val+1 < n
  · let t : Fin n := ⟨i.val+1,hi⟩
    rw [Finset.sum_eq_single t]
    · simp [v5ActualLaurentCompanionMatrix,hi,t]
    · intro j _ hj
      have hj' : j.val ≠ i.val+1 := fun h => hj (Fin.ext h)
      simp [v5ActualLaurentCompanionMatrix,hi,hj']
    · intro ht
      exact (ht (Finset.mem_univ t)).elim
  · have he : i.val+1 = n := by omega
    rw [he]
    let ι := (algebraicClosure ℚ ℂ).val.toRingHom
    let E := arithmeticLaurentEvaluation z
    let S := ∑ j : Fin n, (p j.val).eval₂ ι (z : ℂ) * iteratedDeriv j.val f (z : ℂ)
    have h0 := hrow (z : ℂ)
    unfold v5RowResidual at h0
    rw [Finset.sum_range_succ, ← Fin.sum_univ_eq_sum_range] at h0
    change S + (p n).eval₂ ι (z : ℂ) * iteratedDeriv n f (z : ℂ) = 0 at h0
    have h1 : iteratedDeriv n f (z : ℂ) = -(E L * S) := by
      have h := congrArg (fun x : ℂ => E L * x) h0
      change E L * (S + (p n).eval₂ ι (z : ℂ) * iteratedDeriv n f (z : ℂ)) = E L * 0 at h
      rw [mul_add, ← mul_assoc, hL z, one_mul, mul_zero] at h
      exact eq_neg_of_add_eq_zero_right (by simpa only [add_comm] using h)
    rw [h1]
    dsimp only [S]
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [v5ActualLaurentCompanionMatrix,hi,if_false,map_neg,map_mul,neg_mul]
    have hval : E (Polynomial.toLaurent (p j.val)) = (p j.val).eval₂ ι (z : ℂ) :=
      LaurentPolynomial.eval₂_toLaurent _ _ _
    change -(E L * ((p j.val).eval₂ ι (z : ℂ) * iteratedDeriv j.val f (z : ℂ))) =
      -(E L * E (Polynomial.toLaurent (p j.val)) * iteratedDeriv j.val f (z : ℂ))
    rw [hval,mul_assoc]

/-- Disjoint union of two literal actual systems without replacing their solutions. -/
theorem v5_actual_laurent_sum_system {ι κ : Type} [Fintype ι] [Fintype κ]
    (F : ι → entireFunctionAlgebra) (G : κ → entireFunctionAlgebra)
    (A : Matrix ι ι (LaurentPolynomial AlgebraicComplex))
    (B : Matrix κ κ (LaurentPolynomial AlgebraicComplex))
    (hF : ∀ (z : ℂˣ) i, deriv (F i).val (z : ℂ) =
      ∑ j, arithmeticLaurentEvaluation z (A i j) * (F j).val (z : ℂ))
    (hG : ∀ (z : ℂˣ) i, deriv (G i).val (z : ℂ) =
      ∑ j, arithmeticLaurentEvaluation z (B i j) * (G j).val (z : ℂ)) :
    ∀ (z : ℂˣ) (i : ι ⊕ κ), deriv (Sum.elim F G i).val (z : ℂ) =
      ∑ j, arithmeticLaurentEvaluation z (Matrix.fromBlocks A 0 0 B i j) *
        (Sum.elim F G j).val (z : ℂ) := by
  intro z i
  cases i with
  | inl i =>
    rw [Fintype.sum_sum_type]
    simpa only [Sum.elim_inl,Sum.elim_inr,Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂,Matrix.zero_apply,map_zero,zero_mul,Finset.sum_const_zero,add_zero] using hF z i
  | inr i =>
    rw [Fintype.sum_sum_type]
    simpa only [Sum.elim_inl,Sum.elim_inr,Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂,Matrix.zero_apply,map_zero,zero_mul,Finset.sum_const_zero,zero_add] using hG z i

#print axioms v5_actual_laurent_companion_rows
#print axioms v5_actual_laurent_sum_system
end StrictEUnit
