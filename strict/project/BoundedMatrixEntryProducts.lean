import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
One fixed finite family contains every product of at most r entries of W.
Determinants of all row selections of W*C, with C constant and at most r
columns, lie in its K-span. No rank, invertibility or differential premise.
-/
noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

/-- Include every length from zero to r. The length-zero product is one. -/
def boundedMatrixEntryProduct {L : Type*} [CommMonoid L] {r : ℕ}
    (W : Matrix (Fin r) (Fin r) L)
    (u : Σ d : Fin (r+1), Fin d.val → Fin r × Fin r) : L :=
  ∏ j, W (u.2 j).1 (u.2 j).2

/-- The fixed family includes one even when r=0. -/
theorem one_mem_boundedMatrixEntryProduct_span
    {K L : Type*} [Field K] [Field L] [Algebra K L] {r : ℕ}
    (W : Matrix (Fin r) (Fin r) L) :
    (1 : L) ∈ Submodule.span K (Set.range (boundedMatrixEntryProduct W)) := by
  classical
  apply Submodule.subset_span
  refine ⟨⟨⟨0, Nat.zero_lt_succ r⟩, fun j => Fin.elim0 j⟩, ?_⟩
  simp only [boundedMatrixEntryProduct, Fin.prod_univ_zero]

/-- Direct determinant expansion, not Cauchy-Binet: every summand is a
constant coefficient times one of the SAME bounded products of W entries.
The row-selection map need not be injective. -/
theorem constantMatrix_rowSelection_det_mem_product_span
    {K L : Type*} [Field K] [Field L] [Algebra K L] {r s : ℕ}
    (W : Matrix (Fin r) (Fin r) L) (hs : s ≤ r)
    (C : Matrix (Fin r) (Fin s) K) (ρ : Fin s → Fin r) :
    ((W * C.map (algebraMap K L)).submatrix ρ id).det ∈
      Submodule.span K (Set.range (boundedMatrixEntryProduct W)) := by
  classical
  let S : Submodule K L :=
    Submodule.span K (Set.range (boundedMatrixEntryProduct W))
  rw [Matrix.det_apply']
  apply S.sum_mem
  intro σ hσ
  have hexpand :
      (∏ j : Fin s, ((W * C.map (algebraMap K L)).submatrix ρ id) (σ j) j) =
        ∑ k : Fin s → Fin r,
          (∏ j : Fin s, W (ρ (σ j)) (k j)) *
            algebraMap K L (∏ j : Fin s, C (k j) j) := by
    simp only [Matrix.submatrix_apply, id_eq, Matrix.mul_apply, Matrix.map_apply,
      Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.prod_mul_distrib, map_prod]
  rw [hexpand, Finset.mul_sum]
  apply S.sum_mem
  intro k hk
  have hgen : (∏ j : Fin s, W (ρ (σ j)) (k j)) ∈ S := by
    apply Submodule.subset_span
    exact ⟨⟨⟨s, Nat.lt_succ_of_le hs⟩, fun j => (ρ (σ j), k j)⟩, rfl⟩
  have hc := S.smul_mem
    ((((Equiv.Perm.sign σ : ℤ) : K)) * ∏ j : Fin s, C (k j) j) hgen
  simpa only [Algebra.smul_def, map_mul, map_intCast,
    mul_comm, mul_left_comm, mul_assoc] using hc

end StrictEUnit
end
