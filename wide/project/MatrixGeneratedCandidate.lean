import MatrixGeneratedDifferentialAlgebra
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.FiniteType

/-! Genuine finite-type matrix-generated differential algebra and its fundamental
matrix. The ambient constants hypothesis is explicit; simplicity is not asserted. -/
noncomputable section
namespace StrictEUnit
variable {B L : Type*} [CommRing B] [Field L] [Algebra B L]
variable {n : Type*} [Fintype n] [DecidableEq n]

def candidateMatrix (Y : Matrix n n L) : Matrix n n (matrixGeneratedAlgebra (B := B) Y) :=
  fun i j => ⟨Y i j, matrixEntryAlgebra_le Y (matrixEntry_mem Y i j)⟩

@[simp] theorem candidateMatrix_coe (Y : Matrix n n L) (i j : n) :
    (candidateMatrix (B := B) Y i j : L) = Y i j := rfl

@[simp] theorem candidateMatrix_det_coe (Y : Matrix n n L) :
    ((candidateMatrix (B := B) Y).det : L) = Y.det := by
  exact (matrixGeneratedAlgebra (B := B) Y).val.map_det _

theorem candidateMatrix_det_isUnit (Y : Matrix n n L) (hdet : Y.det ≠ 0) :
    IsUnit (candidateMatrix (B := B) Y).det := by
  have h : (candidateMatrix (B := B) Y).det = (matrixDetUnit (B := B) Y hdet).val := by
    apply Subtype.ext
    exact candidateMatrix_det_coe Y
  rw [h]
  exact (matrixDetUnit (B := B) Y hdet).isUnit

theorem candidateMatrix_isUnit (Y : Matrix n n L) (hdet : Y.det ≠ 0) :
    IsUnit (candidateMatrix (B := B) Y) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (candidateMatrix_det_isUnit Y hdet)

theorem candidateMatrix_ode (dB : Derivation ℤ B B) (dL : Derivation ℤ L L)
    (Y : Matrix n n L) (A : Matrix n n B)
    (hbase : ∀ b, dL (algebraMap B L b) = algebraMap B L (dB b))
    (hode : ∀ i j, dL (Y i j) = ∑ l, algebraMap B L (A i l) * Y l j) :
    (candidateMatrix (B := B) Y).map (matrixGeneratedDerivation dB dL Y A hbase hode) =
      A.map (algebraMap B (matrixGeneratedAlgebra (B := B) Y)) * candidateMatrix Y := by
  ext i j
  change dL (Y i j) = _
  simpa [Matrix.mul_apply] using hode i j

@[instance] theorem candidate_finiteType (Y : Matrix n n L) :
    Algebra.FiniteType B (matrixGeneratedAlgebra (B := B) Y) := by
  apply (Subalgebra.fg_iff_finiteType _).mp
  exact Subalgebra.fg_def.mpr ⟨_, (Set.finite_range _).insert _, rfl⟩

/-- Constants descend from the actual ambient constant-field statement.
No claim about existence of such an ambient field is hidden here. -/
theorem candidate_constants {k : Type*} [Field k] [Algebra k B] [Algebra k L]
    [IsScalarTower k B L]
    (dB : Derivation ℤ B B) (dL : Derivation ℤ L L)
    (Y : Matrix n n L) (A : Matrix n n B)
    (hbase : ∀ b, dL (algebraMap B L b) = algebraMap B L (dB b))
    (hode : ∀ i j, dL (Y i j) = ∑ l, algebraMap B L (A i l) * Y l j)
    (hconstants : ∀ x : L, dL x = 0 ↔ ∃ c : k, algebraMap k L c = x)
    (x : matrixGeneratedAlgebra (B := B) Y) :
    matrixGeneratedDerivation dB dL Y A hbase hode x = 0 ↔
      ∃ c : k, algebraMap k (matrixGeneratedAlgebra (B := B) Y) c = x := by
  constructor
  · intro hx
    have hxL : dL (x : L) = 0 := congrArg Subtype.val hx
    obtain ⟨c,hc⟩ := (hconstants x).mp hxL
    refine ⟨c, Subtype.ext ?_⟩
    simpa using hc
  · rintro ⟨c,rfl⟩
    apply Subtype.ext
    change dL (algebraMap k L c) = 0
    exact (hconstants _).mpr ⟨c,rfl⟩

#print axioms candidateMatrix
#print axioms candidateMatrix_coe
#print axioms candidateMatrix_det_coe
#print axioms candidateMatrix_det_isUnit
#print axioms candidateMatrix_isUnit
#print axioms candidateMatrix_ode
#print axioms candidate_finiteType
#print axioms candidate_constants
end StrictEUnit
