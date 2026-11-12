import FundamentalMatrixConstants
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Polynomial.Derivation

/-! Differential stability of determinantal ideals: intermediate steps
for the finite differential-module projectivity argument.

The connection equation on a finite rectangular matrix is explicit. It is
not yet derived here from a presented module with connection. Noetherianity,
local rank-to-freeness, and the final local-to-global projectivity step are
not conclusions of this module. No field, characteristic-zero, torsion-free,
or regularity assumption is needed for the determinantal stability proof. -/
open scoped BigOperators
noncomputable section
namespace StrictEUnit
variable {k B : Type*} [CommRing k] [CommRing B] [Algebra k B]

/-- Finite product Leibniz, without division or regularity hypotheses. -/
theorem derivation_finset_prod {ι : Type*} [DecidableEq ι]
    (δ : Derivation k B B) (s : Finset ι) (f : ι → B) :
    δ (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * δ (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, δ.leibniz, smul_eq_mul, smul_eq_mul, ih,
      Finset.sum_insert ha, Finset.erase_insert ha, Finset.mul_sum]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hia : i ≠ a := by intro h; subst i; exact ha hi
    rw [Finset.erase_insert_of_ne hia.symm, Finset.prod_insert
      (fun h => ha (Finset.mem_of_mem_erase h))]
    ring

/-- Column-update determinant Leibniz formula over an arbitrary differential ring. -/
theorem derivation_det {n : Type*} [Fintype n] [DecidableEq n]
    (δ : Derivation k B B) (A : Matrix n n B) :
    δ A.det = ∑ j, (A.updateCol j (fun i => δ (A i j))).det := by
  rw [Matrix.det_apply, map_sum]
  simp only [Units.smul_def, map_zsmul, derivation_finset_prod, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Matrix.det_apply]
  simp only [Units.smul_def]
  apply Finset.sum_congr rfl
  intro σ hσ
  congr 1
  rw [← Finset.prod_erase_mul Finset.univ
    (fun i => (A.updateCol j (fun row => δ (A row j))) (σ i) i) (Finset.mem_univ j)]
  simp only [Matrix.updateCol_apply, if_pos rfl]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [if_neg (Finset.ne_of_mem_erase hi)]

theorem derivation_det_rows {n : Type*} [Fintype n] [DecidableEq n]
    (δ : Derivation k B B) (A : Matrix n n B) :
    δ A.det = ∑ i, (A.updateRow i (fun j => δ (A i j))).det := by
  have h := derivation_det δ A.transpose
  rw [Matrix.det_transpose] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Matrix.updateCol_transpose, Matrix.det_transpose]
  rfl

/-- The two coordinate descriptions of the determinant's linear variation agree.
Proved algebraically by applying polynomial differentiation to A+X D. -/
theorem determinant_variation_rows_cols {n : Type*} [Fintype n] [DecidableEq n]
    (A D : Matrix n n B) :
    (∑ j, (A.updateCol j (fun i => D i j)).det) =
      ∑ i, (A.updateRow i (fun j => D i j)).det := by
  let M : Matrix n n (Polynomial B) :=
    fun i j => Polynomial.C (A i j) + Polynomial.X * Polynomial.C (D i j)
  have h := (derivation_det (Polynomial.derivative' :
      Derivation B (Polynomial B) (Polynomial B)) M).symm.trans
    (derivation_det_rows Polynomial.derivative' M)
  have he := congrArg (Polynomial.evalRingHom (0:B)) h
  simp only [map_sum, RingHom.map_det] at he
  convert he using 1 <;>
    apply Finset.sum_congr rfl <;> intro j hj <;> congr 1 <;> ext a b <;>
    simp [M, Matrix.updateCol_apply, Matrix.updateRow_apply, Polynomial.derivative'_apply,
      Polynomial.derivative_add, Polynomial.derivative_mul]
  all_goals split_ifs <;> simp_all

theorem det_updateRow_finset_sum {n α : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n B) (i:n) (s:Finset α) (g:α → n → B) :
    (A.updateRow i (∑ a ∈ s, g a)).det = ∑ a ∈ s, (A.updateRow i (g a)).det :=
  Matrix.detRowAlternating.map_update_sum s i g A

theorem det_updateCol_finset_sum {n α : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n B) (i:n) (s:Finset α) (g:α → n → B) :
    (A.updateCol i (∑ a ∈ s, g a)).det = ∑ a ∈ s, (A.updateCol i (g a)).det := by
  rw [← Matrix.det_transpose, ← Matrix.updateRow_transpose, det_updateRow_finset_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Matrix.updateRow_transpose, Matrix.det_transpose]

/-- All r-minors, allowing arbitrary index maps (repeated rows/columns give zero). -/
def matrixMinorIdeal {m n : Type*} (r : ℕ) (A : Matrix m n B) : Ideal B :=
  Ideal.span {x | ∃ u : Fin r → m, ∃ v : Fin r → n, x = (A.submatrix u v).det}

theorem matrixMinor_mem {m n : Type*} (r:ℕ) (A:Matrix m n B)
    (u:Fin r → m) (v:Fin r → n) : (A.submatrix u v).det ∈ matrixMinorIdeal r A :=
  Ideal.subset_span ⟨u,v,rfl⟩

theorem derivation_minor_decomposition {m n : Type*} [Fintype m] [Fintype n]
    (δ : Derivation k B B) (r : ℕ) (A : Matrix m n B)
    (P : Matrix m m B) (Q : Matrix n n B)
    (hA : ∀ i j, δ (A i j) = (P*A) i j + (A*Q) i j)
    (u : Fin r → m) (v : Fin r → n) :
    δ (A.submatrix u v).det =
      (∑ i, ((A.submatrix u v).updateRow i (fun j => (P*A) (u i) (v j))).det) +
      ∑ j, ((A.submatrix u v).updateCol j (fun i => (A*Q) (u i) (v j))).det := by
  rw [derivation_det]
  have hd (j:Fin r) : (fun i => δ ((A.submatrix u v) i j)) =
      (fun i => (P*A) (u i) (v j)) + (fun i => (A*Q) (u i) (v j)) := by
    funext i
    exact hA (u i) (v j)
  simp_rw [hd, Matrix.det_updateCol_add]
  rw [Finset.sum_add_distrib]
  congr 1
  exact determinant_variation_rows_cols (A.submatrix u v) ((P*A).submatrix u v)

theorem minor_left_variation_mem {m n : Type*} [Fintype m]
    (r:ℕ) (A:Matrix m n B) (P:Matrix m m B)
    (u:Fin r → m) (v:Fin r → n) (i:Fin r) :
    ((A.submatrix u v).updateRow i (fun j => (P*A) (u i) (v j))).det ∈
      matrixMinorIdeal r A := by
  classical
  have hrow : (fun j => (P*A) (u i) (v j)) =
      ∑ l, P (u i) l • (fun j => A l (v j)) := by
    funext j
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hrow, det_updateRow_finset_sum]
  apply Submodule.sum_mem
  intro l hl
  rw [Matrix.det_updateRow_smul]
  apply Ideal.mul_mem_left
  have heq : (A.submatrix u v).updateRow i (fun j => A l (v j)) =
      A.submatrix (Function.update u i l) v := by
    ext a b
    by_cases ha : a = i <;>
      simp [Matrix.updateRow_apply, Matrix.submatrix_apply, Function.update_apply, ha]
  rw [heq]
  exact matrixMinor_mem r A _ _

theorem minor_right_variation_mem {m n : Type*} [Fintype n]
    (r:ℕ) (A:Matrix m n B) (Q:Matrix n n B)
    (u:Fin r → m) (v:Fin r → n) (j:Fin r) :
    ((A.submatrix u v).updateCol j (fun i => (A*Q) (u i) (v j))).det ∈
      matrixMinorIdeal r A := by
  classical
  have hcol : (fun i => (A*Q) (u i) (v j)) =
      ∑ l, Q l (v j) • (fun i => A (u i) l) := by
    funext i
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro l hl
    exact mul_comm _ _
  rw [hcol, det_updateCol_finset_sum]
  apply Submodule.sum_mem
  intro l hl
  rw [Matrix.det_updateCol_smul]
  apply Ideal.mul_mem_left
  have heq : (A.submatrix u v).updateCol j (fun i => A (u i) l) =
      A.submatrix u (Function.update v j l) := by
    ext a b
    by_cases hb : b = j <;>
      simp [Matrix.updateCol_apply, Matrix.submatrix_apply, Function.update_apply, hb]
  rw [heq]
  exact matrixMinor_mem r A _ _

/-- Each actual minor has derivative in its determinantal ideal. -/
theorem derivation_minor_mem {m n : Type*} [Fintype m] [Fintype n]
    (δ : Derivation k B B) (r:ℕ) (A:Matrix m n B)
    (P:Matrix m m B) (Q:Matrix n n B)
    (hA : ∀ i j, δ (A i j) = (P*A) i j + (A*Q) i j)
    (u:Fin r → m) (v:Fin r → n) :
    δ (A.submatrix u v).det ∈ matrixMinorIdeal r A := by
  rw [derivation_minor_decomposition δ r A P Q hA u v]
  apply Ideal.add_mem
  · apply Submodule.sum_mem
    intro i hi
    exact minor_left_variation_mem r A P u v i
  · apply Submodule.sum_mem
    intro j hj
    exact minor_right_variation_mem r A Q u v j

/-- Stability on generators extends to their whole ideal by Leibniz. -/
theorem ideal_span_derivation_stable (δ : Derivation k B B) (s : Set B)
    (hs : ∀ x ∈ s, δ x ∈ Ideal.span s) :
    ∀ x ∈ Ideal.span s, δ x ∈ Ideal.span s := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => simpa only [map_zero] using (Ideal.span s).zero_mem
  | add x y hx hy ihx ihy =>
    rw [map_add]
    exact (Ideal.span s).add_mem ihx ihy
  | smul b x hx ih =>
    change δ (b*x) ∈ Ideal.span s
    rw [δ.leibniz, smul_eq_mul, smul_eq_mul]
    exact (Ideal.span s).add_mem ((Ideal.span s).mul_mem_left b ih)
      ((Ideal.span s).mul_mem_right (δ b) hx)

/-- All determinantal ideals are differential-stable under the actual
presentation-matrix connection equation δA=P A+A Q. -/
theorem matrixMinorIdeal_stable {m n : Type*} [Fintype m] [Fintype n]
    (δ : Derivation k B B) (r:ℕ) (A:Matrix m n B)
    (P:Matrix m m B) (Q:Matrix n n B)
    (hA : ∀ i j, δ (A i j) = (P*A) i j + (A*Q) i j) :
    ∀ x ∈ matrixMinorIdeal r A, δ x ∈ matrixMinorIdeal r A := by
  apply ideal_span_derivation_stable
  rintro x ⟨u,v,rfl⟩
  exact derivation_minor_mem δ r A P Q hA u v

/-- Differential simplicity forces each actual minor ideal to be zero or unit.
This is a determinantal conclusion, not yet a projectivity theorem. -/
theorem matrixMinorIdeal_eq_bot_or_top {m n : Type*} [Fintype m] [Fintype n]
    (δ : Derivation k B B)
    (hsimple : ∀ I : Ideal B, (∀ x ∈ I, δ x ∈ I) → I ≠ ⊥ → I = ⊤)
    (r:ℕ) (A:Matrix m n B) (P:Matrix m m B) (Q:Matrix n n B)
    (hA : ∀ i j, δ (A i j) = (P*A) i j + (A*Q) i j) :
    matrixMinorIdeal r A = ⊥ ∨ matrixMinorIdeal r A = ⊤ := by
  by_cases hz : matrixMinorIdeal r A = ⊥
  · exact Or.inl hz
  · exact Or.inr (hsimple _ (matrixMinorIdeal_stable δ r A P Q hA) hz)

end StrictEUnit

#print axioms StrictEUnit.derivation_finset_prod
#print axioms StrictEUnit.derivation_det
#print axioms StrictEUnit.derivation_det_rows
#print axioms StrictEUnit.determinant_variation_rows_cols
#print axioms StrictEUnit.det_updateRow_finset_sum
#print axioms StrictEUnit.det_updateCol_finset_sum
#print axioms StrictEUnit.matrixMinorIdeal
#print axioms StrictEUnit.matrixMinor_mem
#print axioms StrictEUnit.derivation_minor_decomposition
#print axioms StrictEUnit.minor_left_variation_mem
#print axioms StrictEUnit.minor_right_variation_mem
#print axioms StrictEUnit.derivation_minor_mem
#print axioms StrictEUnit.ideal_span_derivation_stable
#print axioms StrictEUnit.matrixMinorIdeal_stable
#print axioms StrictEUnit.matrixMinorIdeal_eq_bot_or_top
