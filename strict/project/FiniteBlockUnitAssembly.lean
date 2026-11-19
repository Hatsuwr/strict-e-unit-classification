import AnalyticResonanceSquareBlock
import Mathlib.Data.Matrix.Block

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {C : Type*} {I : C →Type*} {R : Type*}
  [Fintype C] [DecidableEq C] [∀ c,Fintype (I c)] [∀ c,DecidableEq (I c)] [CommRing R]

/-- Block units combine into an actual square unit on the dependent disjoint union. -/
def finiteBlockUnit (Z : ∀ c,(Matrix (I c) (I c) R)ˣ) :
    (Matrix (Σ c,I c) (Σ c,I c) R)ˣ where
  val := Matrix.blockDiagonal' (fun c =>(Z c).val)
  inv := Matrix.blockDiagonal' (fun c =>((Z c)⁻¹).val)
  val_inv := by
    rw [← Matrix.blockDiagonal'_mul]
    have he : (fun c =>(Z c).val*((Z c)⁻¹).val)=(1 : ∀ c,Matrix (I c) (I c) R) := by
      funext c;exact (Z c).val_inv
    rw [he,Matrix.blockDiagonal'_one]
  inv_val := by
    rw [← Matrix.blockDiagonal'_mul]
    have he : (fun c =>((Z c)⁻¹).val*(Z c).val)=(1 : ∀ c,Matrix (I c) (I c) R) := by
      funext c;exact (Z c).inv_val
    rw [he,Matrix.blockDiagonal'_one]

theorem finiteBlockUnit_row (Z : ∀ c,(Matrix (I c) (I c) R)ˣ)
    (f : ∀ c,I c →R) (c : C) (j : I c) :
    (∑ i : Σ c,I c,f i.1 i.2*(finiteBlockUnit Z).val i ⟨c,j⟩)=
      ∑ i : I c,f c i*(Z c).val i j := by
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single c]
  · simp only [finiteBlockUnit,Matrix.blockDiagonal'_apply_eq]
  · intro b hb hbc
    simp only [finiteBlockUnit,Matrix.blockDiagonal'_apply_ne _ _ _ hbc,
      mul_zero,Finset.sum_const_zero]
  · intro hc;exact (hc (Finset.mem_univ c)).elim
end StrictEUnit
end
