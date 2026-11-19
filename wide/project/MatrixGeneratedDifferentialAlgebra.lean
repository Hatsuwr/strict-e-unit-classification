import Mathlib.RingTheory.Derivation.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Adjoin.Basic

/-! Actual matrix-generated candidate differential algebra. No differential
simplicity, constants, faithful flatness, or torsor theorem is asserted. -/
noncomputable section
namespace StrictEUnit
variable {B L : Type*} [CommRing B] [Field L] [Algebra B L]
variable (dB : Derivation ℤ B B) (dL : Derivation ℤ L L)

theorem derivation_adjoin_stable (s : Set L)
    (hbase : ∀ b, dL (algebraMap B L b) = algebraMap B L (dB b))
    (hgen : ∀ x ∈ s, dL x ∈ Algebra.adjoin B s) :
    ∀ x ∈ Algebra.adjoin B s, dL x ∈ Algebra.adjoin B s := by
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact hgen x hx
  | algebraMap b => rw [hbase]; exact (Algebra.adjoin B s).algebraMap_mem _
  | add x y hx hy ihx ihy => rw [map_add]; exact (Algebra.adjoin B s).add_mem ihx ihy
  | mul x y hx hy ihx ihy =>
    rw [dL.leibniz]
    exact (Algebra.adjoin B s).add_mem
      ((Algebra.adjoin B s).mul_mem hx ihy) ((Algebra.adjoin B s).mul_mem hy ihx)

variable {n : Type*} [Fintype n] [DecidableEq n]

def matrixEntryAlgebra (Y : Matrix n n L) : Subalgebra B L :=
  Algebra.adjoin B (Set.range fun ij : n × n => Y ij.1 ij.2)

def matrixGeneratedAlgebra (Y : Matrix n n L) : Subalgebra B L :=
  Algebra.adjoin B (insert Y.det⁻¹ (Set.range fun ij : n × n => Y ij.1 ij.2))

omit [Fintype n] [DecidableEq n] in
theorem matrixEntry_mem (Y : Matrix n n L) (i j : n) :
    Y i j ∈ matrixEntryAlgebra (B := B) Y :=
  Algebra.subset_adjoin ⟨(i,j), rfl⟩

theorem matrixEntryAlgebra_le (Y : Matrix n n L) :
    matrixEntryAlgebra (B := B) Y ≤ matrixGeneratedAlgebra (B := B) Y :=
  Algebra.adjoin_mono (Set.subset_insert _ _)

theorem matrixDet_mem (Y : Matrix n n L) :
    Y.det ∈ matrixEntryAlgebra (B := B) Y := by
  rw [Matrix.det_apply]
  apply Subalgebra.sum_mem
  intro σ hσ
  apply Subalgebra.zsmul_mem
  apply Subalgebra.prod_mem
  intro i hi
  exact matrixEntry_mem Y _ _

omit [DecidableEq n] in
theorem matrixEntryAlgebra_stable (Y : Matrix n n L) (A : Matrix n n B)
    (hbase : ∀ b, dL (algebraMap B L b) = algebraMap B L (dB b))
    (hode : ∀ i j, dL (Y i j) = ∑ l, algebraMap B L (A i l) * Y l j) :
    ∀ x ∈ matrixEntryAlgebra (B := B) Y, dL x ∈ matrixEntryAlgebra (B := B) Y := by
  apply derivation_adjoin_stable dB dL _ hbase
  rintro x ⟨⟨i,j⟩,rfl⟩
  rw [hode]
  apply Subalgebra.sum_mem
  intro l hl
  exact (matrixEntryAlgebra Y).mul_mem ((matrixEntryAlgebra Y).algebraMap_mem _) (matrixEntry_mem Y _ _)

theorem matrixGeneratedAlgebra_stable (Y : Matrix n n L) (A : Matrix n n B)
    (hbase : ∀ b, dL (algebraMap B L b) = algebraMap B L (dB b))
    (hode : ∀ i j, dL (Y i j) = ∑ l, algebraMap B L (A i l) * Y l j) :
    ∀ x ∈ matrixGeneratedAlgebra (B := B) Y, dL x ∈ matrixGeneratedAlgebra (B := B) Y := by
  apply derivation_adjoin_stable dB dL _ hbase
  intro x hx
  rcases hx with rfl | hx
  · rw [dL.leibniz_inv]
    apply Subalgebra.mul_mem
    · exact (matrixGeneratedAlgebra Y).neg_mem ((matrixGeneratedAlgebra Y).pow_mem (Algebra.subset_adjoin (Set.mem_insert _ _)) 2)
    · exact matrixEntryAlgebra_le Y (matrixEntryAlgebra_stable dB dL Y A hbase hode _ (matrixDet_mem Y))
  · exact matrixEntryAlgebra_le Y (matrixEntryAlgebra_stable dB dL Y A hbase hode _ (Algebra.subset_adjoin hx))

/-- Restriction uses the proved stability, not an additional hypothesis. -/
def matrixGeneratedDerivation (Y : Matrix n n L) (A : Matrix n n B)
    (hbase : ∀ b, dL (algebraMap B L b) = algebraMap B L (dB b))
    (hode : ∀ i j, dL (Y i j) = ∑ l, algebraMap B L (A i l) * Y l j) :
    Derivation ℤ (matrixGeneratedAlgebra (B := B) Y) (matrixGeneratedAlgebra (B := B) Y) where
  toFun x := ⟨dL x, matrixGeneratedAlgebra_stable dB dL Y A hbase hode x x.property⟩
  map_add' x y := Subtype.ext (dL.map_add (x : L) (y : L))
  map_smul' r x := Subtype.ext (dL.map_smul r (x : L))
  leibniz' x y := Subtype.ext (dL.leibniz (x : L) (y : L))
  map_one_eq_zero' := Subtype.ext dL.map_one_eq_zero

@[simp] theorem matrixGeneratedDerivation_apply (Y : Matrix n n L) (A : Matrix n n B)
    (hbase : ∀ b, dL (algebraMap B L b) = algebraMap B L (dB b))
    (hode : ∀ i j, dL (Y i j) = ∑ l, algebraMap B L (A i l) * Y l j)
    (x : matrixGeneratedAlgebra (B := B) Y) :
    (matrixGeneratedDerivation dB dL Y A hbase hode x : L) = dL x := rfl

/-- Nonvanishing is needed for invertibility, not for stability. -/
def matrixDetUnit (Y : Matrix n n L) (hdet : Y.det ≠ 0) :
    (matrixGeneratedAlgebra (B := B) Y)ˣ where
  val := ⟨Y.det, matrixEntryAlgebra_le Y (matrixDet_mem Y)⟩
  inv := ⟨Y.det⁻¹, Algebra.subset_adjoin (Set.mem_insert _ _)⟩
  val_inv := Subtype.ext (mul_inv_cancel₀ hdet)
  inv_val := Subtype.ext (inv_mul_cancel₀ hdet)

@[simp] theorem matrixDetUnit_val (Y : Matrix n n L) (hdet : Y.det ≠ 0) :
    (((matrixDetUnit (B := B) Y hdet : (matrixGeneratedAlgebra (B := B) Y)ˣ) :
      matrixGeneratedAlgebra (B := B) Y) : L) = Y.det := rfl

omit [DecidableEq n] in
/-- The entrywise hypothesis is exactly the ordinary matrix differential equation. -/
theorem matrix_ode_entries (Y : Matrix n n L) (A : Matrix n n B)
    (hode : Y.map dL = A.map (algebraMap B L) * Y) :
    ∀ i j, dL (Y i j) = ∑ l, algebraMap B L (A i l) * Y l j := by
  intro i j
  exact congrFun (congrFun hode i) j

#print axioms derivation_adjoin_stable
#print axioms matrixEntryAlgebra
#print axioms matrixGeneratedAlgebra
#print axioms matrixEntry_mem
#print axioms matrixEntryAlgebra_le
#print axioms matrixDet_mem
#print axioms matrixEntryAlgebra_stable
#print axioms matrixGeneratedAlgebra_stable
#print axioms matrixGeneratedDerivation
#print axioms matrixGeneratedDerivation_apply
#print axioms matrixDetUnit
#print axioms matrixDetUnit_val
#print axioms matrix_ode_entries
end StrictEUnit
