import DeterminantalIdealStability
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-! Explicit local Gaussian elimination for a rectangular presentation.
The pivot is a unit determinant, not merely a nonzero determinant.
The selected block decomposition is explicit; extracting such a block from
local determinantal ideals and global projectivity are separate steps. -/
noncomputable section
open Matrix
namespace StrictEUnit
variable {B i j l : Type*} [CommRing B]
  [Fintype i] [DecidableEq i] [Fintype j] [Fintype l]

/-- Projection onto complementary rows after eliminating the pivot columns. -/
def schurCokernelProjection (A : Matrix i i B) (C : Matrix j i B) :
    (i ⊕ j → B) →ₗ[B] (j → B) where
  toFun x := (x ∘ Sum.inr) - C *ᵥ (A⁻¹ *ᵥ (x ∘ Sum.inl))
  map_add' x y := by
    change (x ∘ Sum.inr + y ∘ Sum.inr) - C *ᵥ (A⁻¹ *ᵥ (x ∘ Sum.inl + y ∘ Sum.inl)) = _
    simp only [mulVec_add]
    abel
  map_smul' a x := by
    change (a • (x ∘ Sum.inr)) - C *ᵥ (A⁻¹ *ᵥ (a • (x ∘ Sum.inl))) = _
    simp only [mulVec_smul, smul_sub, RingHom.id_apply]

omit [Fintype j] in
theorem schurCokernelProjection_surjective (A : Matrix i i B) (C : Matrix j i B) :
    Function.Surjective (schurCokernelProjection A C) := by
  intro y
  refine ⟨Sum.elim 0 y, ?_⟩
  change y - C *ᵥ (A⁻¹ *ᵥ (0 : i → B)) = y
  simp

omit [Fintype j] in
/-- Vanishing Schur complement gives the actual kernel/image equality. -/
theorem schurCokernelProjection_ker (A : Matrix i i B) (U : Matrix i l B)
    (C : Matrix j i B) (V : Matrix j l B) (hA : IsUnit A.det)
    (hV : V = C * A⁻¹ * U) :
    LinearMap.ker (schurCokernelProjection A C) =
      LinearMap.range (Matrix.fromBlocks A U C V).mulVecLin := by
  ext x
  constructor
  · intro hx
    have hx' : x ∘ Sum.inr = C *ᵥ (A⁻¹ *ᵥ (x ∘ Sum.inl)) := by
      simpa only [LinearMap.mem_ker, schurCokernelProjection, LinearMap.coe_mk,
        AddHom.coe_mk, sub_eq_zero] using hx
    refine ⟨Sum.elim (A⁻¹ *ᵥ (x ∘ Sum.inl)) 0, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.fromBlocks_mulVec, Function.comp_def,
      Sum.elim_inl, Sum.elim_inr, mulVec_zero, add_zero]
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv A hA, Matrix.one_mulVec]
    ext q
    cases q with
    | inl q => rfl
    | inr q => exact congrFun hx'.symm q
  · rintro ⟨y, rfl⟩
    simp only [LinearMap.mem_ker, schurCokernelProjection, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.mulVecLin_apply, Matrix.fromBlocks_mulVec,
      Function.comp_def, Sum.elim_inl, Sum.elim_inr, mulVec_add]
    change (C *ᵥ (y ∘ Sum.inl) + V *ᵥ (y ∘ Sum.inr)) -
      (C *ᵥ (A⁻¹ *ᵥ (A *ᵥ (y ∘ Sum.inl))) + C *ᵥ (A⁻¹ *ᵥ (U *ᵥ (y ∘ Sum.inr)))) = 0
    rw [mulVec_mulVec (y ∘ Sum.inl) A⁻¹ A, Matrix.nonsing_inv_mul A hA, Matrix.one_mulVec]
    rw [hV, ← mulVec_mulVec, ← mulVec_mulVec]
    abel

omit [Fintype j] [Fintype l] in
/-- Vanishing bordered minors force the full Schur complement to vanish. -/
theorem schurComplement_eq_zero_of_bordered_minors (A : Matrix i i B)
    (U : Matrix i l B) (C : Matrix j i B) (V : Matrix j l B)
    (hA : IsUnit A.det)
    (hborder : ∀ r s, (Matrix.fromBlocks A (fun p (_ : Unit) => U p s)
      (fun (_ : Unit) p => C r p) (fun (_ _ : Unit) => V r s)).det = 0) :
    V = C * A⁻¹ * U := by
  letI : Invertible A := Matrix.invertibleOfIsUnitDet A hA
  ext r s
  have h := hborder r s
  rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv] at h
  have h' : A.det * (V r s - (C * A⁻¹ * U) r s) = 0 := by
    simpa only [Matrix.det_unique, Matrix.sub_apply, Matrix.mul_apply] using h
  exact sub_eq_zero.mp (hA.mul_left_cancel (by simpa using h'))

/-- The cokernel is concretely free on the complementary row indices. -/
def schurCokernelEquiv (A : Matrix i i B) (U : Matrix i l B)
    (C : Matrix j i B) (V : Matrix j l B) (hA : IsUnit A.det)
    (hV : V = C * A⁻¹ * U) :
    ((i ⊕ j → B) ⧸ LinearMap.range (Matrix.fromBlocks A U C V).mulVecLin) ≃ₗ[B]
      (j → B) :=
  (Submodule.quotEquivOfEq _ _ (schurCokernelProjection_ker A U C V hA hV).symm).trans
    ((schurCokernelProjection A C).quotKerEquivOfSurjective
      (schurCokernelProjection_surjective A C))

/-- In particular the actual block-presentation cokernel is projective. -/
theorem blockCokernel_projective (A : Matrix i i B) (U : Matrix i l B)
    (C : Matrix j i B) (V : Matrix j l B) (hA : IsUnit A.det)
    (hborder : ∀ r s, (Matrix.fromBlocks A (fun p (_ : Unit) => U p s)
      (fun (_ : Unit) p => C r p) (fun (_ _ : Unit) => V r s)).det = 0) :
    Module.Projective B
      ((i ⊕ j → B) ⧸ LinearMap.range (Matrix.fromBlocks A U C V).mulVecLin) := by
  exact Module.Projective.of_equiv
    (schurCokernelEquiv A U C V hA
      (schurComplement_eq_zero_of_bordered_minors A U C V hA hborder)).symm

/-- A zero determinantal ideal kills minors with any equivalent finite index type. -/
theorem minor_eq_zero_of_ideal_eq_bot {m n t : Type*} [Fintype t] [DecidableEq t]
    (M : Matrix m n B) (u : t → m) (v : t → n)
    (h : matrixMinorIdeal (Fintype.card t) M = ⊥) : (M.submatrix u v).det = 0 := by
  have hz := matrixMinor_mem (Fintype.card t) M
    (u ∘ (Fintype.equivFin t).symm) (v ∘ (Fintype.equivFin t).symm)
  rw [h, Ideal.mem_bot] at hz
  have he : M.submatrix (u ∘ (Fintype.equivFin t).symm)
      (v ∘ (Fintype.equivFin t).symm) =
      (M.submatrix u v).submatrix (Fintype.equivFin t).symm (Fintype.equivFin t).symm := rfl
  rwa [he, Matrix.det_submatrix_equiv_self] at hz

/-- The zero next-minor ideal supplies the bordered-minor hypothesis. -/
theorem blockCokernel_projective_of_minorIdeal (A : Matrix i i B) (U : Matrix i l B)
    (C : Matrix j i B) (V : Matrix j l B) (hA : IsUnit A.det)
    (hnext : matrixMinorIdeal (Fintype.card i + 1) (Matrix.fromBlocks A U C V) = ⊥) :
    Module.Projective B
      ((i ⊕ j → B) ⧸ LinearMap.range (Matrix.fromBlocks A U C V).mulVecLin) := by
  apply blockCokernel_projective A U C V hA
  intro r s
  have hz := minor_eq_zero_of_ideal_eq_bot (Matrix.fromBlocks A U C V)
    (Sum.map id (fun (_ : Unit) => r)) (Sum.map id (fun (_ : Unit) => s))
    (by simpa using hnext)
  convert hz using 2
  ext x y
  cases x <;> cases y <;> rfl

/-- In a local ring a unit minor ideal contains a unit minor. -/
theorem exists_unit_minor_of_ideal_eq_top [IsLocalRing B] {m n : Type*}
    (r : ℕ) (M : Matrix m n B) (h : matrixMinorIdeal r M = ⊤) :
    ∃ u : Fin r → m, ∃ v : Fin r → n, IsUnit (M.submatrix u v).det := by
  classical
  by_contra hn
  push_neg at hn
  have hle : matrixMinorIdeal r M ≤ IsLocalRing.maximalIdeal B := by
    apply Ideal.span_le.mpr
    rintro x ⟨u, v, rfl⟩
    exact (IsLocalRing.mem_maximalIdeal _).mpr (hn u v)
  rw [h] at hle
  exact (Ideal.IsMaximal.ne_top (inferInstance : (IsLocalRing.maximalIdeal B).IsMaximal)) (top_le_iff.mp hle)

end StrictEUnit

#print axioms StrictEUnit.schurCokernelProjection
#print axioms StrictEUnit.schurCokernelProjection_surjective
#print axioms StrictEUnit.schurCokernelProjection_ker
#print axioms StrictEUnit.schurComplement_eq_zero_of_bordered_minors
#print axioms StrictEUnit.schurCokernelEquiv
#print axioms StrictEUnit.blockCokernel_projective
#print axioms StrictEUnit.minor_eq_zero_of_ideal_eq_bot
#print axioms StrictEUnit.blockCokernel_projective_of_minorIdeal
#print axioms StrictEUnit.exists_unit_minor_of_ideal_eq_top

