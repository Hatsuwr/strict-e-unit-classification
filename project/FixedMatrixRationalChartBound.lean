import BoundedMatrixEntryProducts
import FiniteFamilyRationalRatio
import Mathlib.Algebra.Algebra.Tower

/-!
A uniform rational-chart degree bound from ONE fixed finite product family.
The structural factorization and nonzero pivot determinant are explicit here;
this module does not claim that a differential subspace supplies them.
-/
noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

/-- The precise row-replacement determinant identity. Matrix products have
X on the left, and the replaced row is j, not i. -/
theorem factoredMatrix_row_replacement_det
    {L : Type*} [CommRing L] {r s : ℕ}
    (X V : Matrix (Fin r) (Fin s) L) (M : Matrix (Fin s) (Fin s) L)
    (hfactor : V = X * M) (i : Fin r) (j : Fin s) :
    (M.updateRow j (V i)).det = X i j * M.det := by
  classical
  have hrow : V i = ∑ k : Fin s, X i k • M k := by
    funext l
    rw [hfactor]
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hrow, Matrix.det_updateRow_sum, smul_eq_mul]

/-- D is chosen before the dimension, constant matrix, pivot map and rational
chart. No bounded-coordinate or bounded-denominator assumption occurs.
The embedding is explicit, so an ordinary-point embedding may be used without
changing the original RatFunc variable or the polynomial degrees returned.
No invertibility of W is needed for this algebraic core. -/
theorem exists_uniform_fixedMatrix_rational_chart_bound
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (ι : RatFunc K →ₐ[K] L) {r : ℕ} (W : Matrix (Fin r) (Fin r) L) :
    ∃ D : ℕ, ∀ s : ℕ, s ≤ r →
      ∀ C : Matrix (Fin r) (Fin s) K, ∀ p : Fin s → Fin r,
      ∀ X : Matrix (Fin r) (Fin s) (RatFunc K),
        ((W * C.map (algebraMap K L)).submatrix p id).det ≠ 0 →
        W * C.map (algebraMap K L) =
          X.map ι * ((W * C.map (algebraMap K L)).submatrix p id) →
        ∀ i : Fin r, ∀ j : Fin s,
          ∃ p₁ p₂ : Polynomial K, p₂ ≠ 0 ∧
            p₁.natDegree ≤ D ∧ p₂.natDegree ≤ D ∧
            X i j = algebraMap (Polynomial K) (RatFunc K) p₁ /
              algebraMap (Polynomial K) (RatFunc K) p₂ := by
  classical
  letI : Algebra (RatFunc K) L := ι.toRingHom.toAlgebra
  letI : IsScalarTower K (RatFunc K) L := IsScalarTower.of_algHom ι
  obtain ⟨D, hD⟩ := exists_uniform_finite_family_rational_ratio_bound
    (K := K) (boundedMatrixEntryProduct W)
  refine ⟨D, ?_⟩
  intro s hs C p X hdet hfactor i j
  let V : Matrix (Fin r) (Fin s) L := W * C.map (algebraMap K L)
  let M : Matrix (Fin s) (Fin s) L := V.submatrix p id
  have hden : M.det ∈ Submodule.span K (Set.range (boundedMatrixEntryProduct W)) :=
    constantMatrix_rowSelection_det_mem_product_span W hs C p
  have hupdate : M.updateRow j (V i) =
      V.submatrix (fun k => if k = j then i else p k) id := by
    apply Matrix.ext
    intro k l
    by_cases hkj : k = j <;>
      simp [Matrix.updateRow_apply, Matrix.submatrix_apply, hkj, M]
  have hnum : (M.updateRow j (V i)).det ∈
      Submodule.span K (Set.range (boundedMatrixEntryProduct W)) := by
    rw [hupdate]
    exact constantMatrix_rowSelection_det_mem_product_span W hs C
      (fun k => if k = j then i else p k)
  have hrel : (M.updateRow j (V i)).det =
      algebraMap (RatFunc K) L (X i j) * M.det := by
    change (M.updateRow j (V i)).det = ι (X i j) * M.det
    exact factoredMatrix_row_replacement_det (X.map ι) V M hfactor i j
  exact hD (M.updateRow j (V i)).det M.det hnum hden hdet (X i j) hrel

end StrictEUnit
end
