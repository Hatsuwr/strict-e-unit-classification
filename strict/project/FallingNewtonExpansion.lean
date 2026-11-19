import FrobeniusFallingLogFilters
import Mathlib.Algebra.Polynomial.Roots

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Newton coefficients, computed at consecutive natural arguments. -/
def fallingNewtonCoefficient (P : Polynomial K) (n : ℕ) : K :=
  P.eval (n : K) - ∑ k : Fin n,
    fallingNewtonCoefficient P k.val * (n.choose k.val : K)
termination_by n
decreasing_by exact k.isLt

def fallingNewtonSum (P : Polynomial K) (N : ℕ) : Polynomial K :=
  ∑ k ∈ Finset.range (N+1),
    Polynomial.C (fallingNewtonCoefficient P k)*normalizedFallingSymbol (K:=K) k

theorem normalizedFallingSymbol_natDegree_le (m : ℕ) :
    (normalizedFallingSymbol (K:=K) m).natDegree≤m := by
  exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)

theorem fallingNewtonSum_natDegree_le (P : Polynomial K) (N : ℕ) :
    (fallingNewtonSum P N).natDegree≤N := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    ((normalizedFallingSymbol_natDegree_le k).trans (by have := Finset.mem_range.mp hk; omega))

theorem fallingNewtonSum_eval (P : Polynomial K) (N k : ℕ) (hk : k≤N) :
    (fallingNewtonSum P N).eval (k : K)=P.eval (k : K) := by
  classical
  simp only [fallingNewtonSum,Polynomial.eval_finset_sum,Polynomial.eval_mul,
    Polynomial.eval_C,normalizedFallingSymbol_eval,Ring.choose_natCast]
  have hs : (∑ i ∈ Finset.range (N+1),fallingNewtonCoefficient P i*(k.choose i : K))=
      ∑ i ∈ Finset.range (k+1),fallingNewtonCoefficient P i*(k.choose i : K) := by
    symm
    apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hk))
    intro i hi hnot
    have hki : k < i := by simp only [Finset.mem_range] at hnot; omega
    rw [Nat.choose_eq_zero_of_lt hki,Nat.cast_zero,mul_zero]
  rw [hs,Finset.sum_range_succ,fallingNewtonCoefficient]
  simp only [Nat.choose_self,Nat.cast_one,mul_one]
  rw [← Fin.sum_univ_eq_sum_range (fun i => fallingNewtonCoefficient P i*(k.choose i : K)) k]
  ring

/-- No factorial loss: an integral scalar clearing the values also clears
all Newton coefficients needed at that same degree. -/
theorem fallingNewtonCoefficient_integral (P : Polynomial K) (D : K) (N : ℕ)
    (hP : ∀ k,k≤N → IsIntegral ℤ (D*P.eval (k : K))) :
    ∀ k,k≤N → IsIntegral ℤ (D*fallingNewtonCoefficient P k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    rw [fallingNewtonCoefficient,mul_sub,Finset.mul_sum]
    apply IsIntegral.sub (hP k hk)
    apply IsIntegral.sum
    intro i hi
    have hik := i.isLt
    simpa only [mul_assoc] using (ih i.val hik (Nat.le_trans (Nat.le_of_lt hik) hk)).mul
      (ordinaryJet_natCast_integral (K:=K) (k.choose i))

/-- Finite, exact Newton expansion, not an asymptotic approximation. -/
theorem fallingNewtonSum_eq (P : Polynomial K) (N : ℕ) (hP : P.natDegree≤N) :
    fallingNewtonSum P N=P := by
  apply sub_eq_zero.mp
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (fallingNewtonSum P N-P) (f:=fun i : Fin (N+1) => (i.val : K))
  · intro i j h
    exact Fin.ext (Nat.cast_injective h)
  · intro i
    rw [Polynomial.eval_sub,fallingNewtonSum_eval P N i.val (by omega),sub_self]
  · rw [Fintype.card_fin]
    exact Nat.lt_succ_of_le ((Polynomial.natDegree_sub_le _ _).trans
      (max_le (fallingNewtonSum_natDegree_le P N) hP))

end StrictEUnit
end
