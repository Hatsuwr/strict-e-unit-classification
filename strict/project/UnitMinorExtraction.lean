import LocalMinorCokernel
import Mathlib.Logic.Equiv.Set

/-! Extracting a genuine unit minor into a block presentation, with no
rank, local-freeness, or projectivity premise. -/
noncomputable section
open Matrix
namespace StrictEUnit
variable {B m n : Type*} [CommRing B] [Fintype m] [Fintype n]

omit [Fintype m] [Fintype n] in
/-- A unit determinant cannot have repeated selected rows or columns. -/
theorem unit_minor_indices_injective [Nontrivial B] (r : ℕ) (M : Matrix m n B)
    (u : Fin r → m) (v : Fin r → n) (h : IsUnit (M.submatrix u v).det) :
    Function.Injective u ∧ Function.Injective v := by
  constructor
  · intro a b hab
    by_contra hn
    exact h.ne_zero (Matrix.det_zero_of_row_eq hn (by ext q; simp [Matrix.submatrix, hab]))
  · intro a b hab
    by_contra hn
    exact h.ne_zero (Matrix.det_zero_of_column_eq hn (by intro q; simp [Matrix.submatrix, hab]))

/-- Extend an injective selection to an equivalence with its complement. -/
def selectionEquiv {t : Type*} (u : t → m) (hu : Function.Injective u) :
    t ⊕ {x : m // x ∉ Set.range u} ≃ m := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective u hu) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range u))

omit [Fintype m] in
@[simp] theorem selectionEquiv_inl {t : Type*} (u : t → m) (hu : Function.Injective u)
    (x : t) : selectionEquiv u hu (Sum.inl x) = u x := rfl

/-- Changing finite row/column coordinates preserves the actual cokernel. -/
def matrixCokernelReindexEquiv {m' n' : Type*} [Fintype m'] [Fintype n']
    (M : Matrix m n B) (e : m ≃ m') (f : n ≃ n') :
    ((m → B) ⧸ LinearMap.range M.mulVecLin) ≃ₗ[B]
      ((m' → B) ⧸ LinearMap.range (Matrix.reindex e f M).mulVecLin) := by
  apply Submodule.Quotient.equiv _ _ (LinearEquiv.funCongrLeft B B e.symm)
  rw [Matrix.mulVecLin_reindex, ← LinearMap.comp_assoc, LinearMap.range_comp_of_range_eq_top _
    (LinearEquiv.range (LinearEquiv.funCongrLeft B B f))]
  exact (LinearMap.range_comp _ _).symm

omit [Fintype m] [Fintype n] in
/-- Zero minor ideals remain zero under arbitrary row/column selection. -/
theorem matrixMinorIdeal_submatrix_eq_bot {m' n' : Type*} (r : ℕ) (M : Matrix m n B)
    (u : m' → m) (v : n' → n) (h : matrixMinorIdeal r M = ⊥) :
    matrixMinorIdeal r (M.submatrix u v) = ⊥ := by
  apply le_antisymm _ bot_le
  apply Ideal.span_le.mpr
  rintro x ⟨a,b,rfl⟩
  have hx := matrixMinor_mem r M (u ∘ a) (v ∘ b)
  rw [h] at hx
  exact hx

/-- An arbitrary unit r-minor plus zero (r+1)-minor ideal gives a projective cokernel. -/
theorem matrixCokernel_projective_of_unit_minor [Nontrivial B]
    (r : ℕ) (M : Matrix m n B) (u : Fin r → m) (v : Fin r → n)
    (hu : IsUnit (M.submatrix u v).det) (hz : matrixMinorIdeal (r+1) M = ⊥) :
    Module.Projective B ((m → B) ⧸ LinearMap.range M.mulVecLin) := by
  classical
  obtain ⟨hi,hj⟩ := unit_minor_indices_injective r M u v hu
  let e := selectionEquiv u hi
  let f := selectionEquiv v hj
  let A := M.submatrix u v
  let U : Matrix (Fin r) {x : n // x ∉ Set.range v} B := fun a b => M (u a) b
  let C : Matrix {x : m // x ∉ Set.range u} (Fin r) B := fun a b => M a (v b)
  let V : Matrix {x : m // x ∉ Set.range u} {x : n // x ∉ Set.range v} B := fun a b => M a b
  have heq : Matrix.reindex e.symm f.symm M = Matrix.fromBlocks A U C V := by
    ext a b
    cases a <;> cases b <;> rfl
  have hzero : matrixMinorIdeal (Fintype.card (Fin r)+1) (Matrix.fromBlocks A U C V) = ⊥ := by
    rw [← heq]
    simpa only [Fintype.card_fin] using matrixMinorIdeal_submatrix_eq_bot (r+1) M e f hz
  letI := blockCokernel_projective_of_minorIdeal A U C V hu hzero
  have hp : Module.Projective B
      ((_ → B) ⧸ LinearMap.range (Matrix.reindex e.symm f.symm M).mulVecLin) := by
    rw [heq]
    infer_instance
  letI := hp
  exact Module.Projective.of_equiv (matrixCokernelReindexEquiv M e.symm f.symm).symm

/-- The local criterion uses only the two actual determinantal ideals. -/
theorem matrixCokernel_projective_of_minorIdeals [IsLocalRing B]
    (r : ℕ) (M : Matrix m n B) (ht : matrixMinorIdeal r M = ⊤)
    (hz : matrixMinorIdeal (r+1) M = ⊥) :
    Module.Projective B ((m → B) ⧸ LinearMap.range M.mulVecLin) := by
  obtain ⟨u,v,hu⟩ := exists_unit_minor_of_ideal_eq_top r M ht
  exact matrixCokernel_projective_of_unit_minor r M u v hu hz

end StrictEUnit
#print axioms StrictEUnit.unit_minor_indices_injective
#print axioms StrictEUnit.selectionEquiv
#print axioms StrictEUnit.selectionEquiv_inl
#print axioms StrictEUnit.matrixCokernelReindexEquiv
#print axioms StrictEUnit.matrixMinorIdeal_submatrix_eq_bot
#print axioms StrictEUnit.matrixCokernel_projective_of_unit_minor
#print axioms StrictEUnit.matrixCokernel_projective_of_minorIdeals
