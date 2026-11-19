import MatrixDualBinomial

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {k B : Type*} [Field k] [Field B] [Algebra k B]

/-- Adjoin a constant forcing coordinate FIRST; the original coordinates
are the successors. Its equation is c'=0, y'=A*y+b*c. -/
def constantForcingConnection {r : ℕ} (A : Matrix (Fin r) (Fin r) B)
    (b : Fin r → B) : Matrix (Fin (r+1)) (Fin (r+1)) B :=
  fun i =>Fin.cases (fun _ =>0) (fun i =>Fin.cases (b i) (fun j =>A i j)) i

def constantForcingColumn (d : Derivation k B B) {r : ℕ}
    (A : Matrix (Fin r) (Fin r) B) (b : Fin r → B) : ℕ → Fin r → B
  | 0 => fun _ =>0
  | m+1 => fun i =>d (constantForcingColumn d A b m i)+
      ∑ j,matrixConnectionSequence d A m i j*b j

/-- Every block of the literal higher connection is computed, including
order zero and the forcing coordinate. -/
theorem constantForcingConnection_sequence (d : Derivation k B B) {r : ℕ}
    (A : Matrix (Fin r) (Fin r) B) (b : Fin r → B) (m : ℕ) :
    (∀ j,matrixConnectionSequence d (constantForcingConnection A b) m 0 j=
      if m=0 ∧ j=0 then 1 else 0) ∧
    (∀ i j,matrixConnectionSequence d (constantForcingConnection A b) m i.succ j.succ=
      matrixConnectionSequence d A m i j) ∧
    (∀ i,matrixConnectionSequence d (constantForcingConnection A b) m i.succ 0=
      constantForcingColumn d A b m i) := by
  classical
  induction m with
  | zero =>
    simp only [matrixConnectionSequence,constantForcingColumn,Matrix.one_apply]
    refine ⟨?_,?_,?_⟩
    · intro j;simp [eq_comm]
    · intro i j;simp
    · intro i;simp
  | succ m ih =>
    rcases ih with ⟨htop,hmain,hcol⟩
    simp only [matrixConnectionSequence,Matrix.add_apply,Matrix.map_apply,Matrix.mul_apply,
      Fin.sum_univ_succ,constantForcingConnection,Fin.cases_zero,Fin.cases_succ,
      mul_zero,zero_add,hmain,hcol,htop,constantForcingColumn]
    refine ⟨?_,?_,?_⟩
    · intro j
      by_cases hm : m=0
      · subst m
        simp only [true_and,if_pos rfl,Fin.succ_ne_zero,and_false,if_false,
          zero_mul,Finset.sum_const_zero,add_zero,map_one,Fin.cases_zero]
        split_ifs <;> simp_all
      · simp [hm]
    · intro i j;trivial
    · intro i;trivial

/-- Exact unnormalized off-diagonal formula. There is only one transition
from the old system into the new constant coordinate. -/
theorem constantForcingColumn_sum (d : Derivation k B B) {r : ℕ}
    (A : Matrix (Fin r) (Fin r) B) (b : Fin r → B) (m : ℕ) (i : Fin r) :
    constantForcingColumn d A b m i=
      ∑ a ∈ Finset.range m,(d : B → B)^[m-1-a]
        (∑ j,matrixConnectionSequence d A a i j*b j) := by
  induction m with
  | zero =>simp [constantForcingColumn]
  | succ m ih =>
    change d (constantForcingColumn d A b m i)+(∑ j,matrixConnectionSequence d A m i j*b j)=_
    rw [ih,map_sum,Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel, Nat.sub_self,Function.iterate_zero_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    have ham : a<m := Finset.mem_range.mp ha
    rw [show m-a=(m-1-a)+1 by omega,Function.iterate_succ_apply']

end StrictEUnit
end
