import MatrixGeneratedCandidate
import PVConstantSurjectivity

/-! Surjectivity for the actual matrix-generated algebra, with no asserted
injectivity, simplicity, or torsor isomorphism. -/
noncomputable section
namespace StrictEUnit
variable {k B L n : Type*} [CommRing k] [CommRing B] [Field L]
  [Algebra k B] [Algebra k L] [Algebra B L] [IsScalarTower k B L]
  [Fintype n] [DecidableEq n]

def candidateMatrixUnit (Y : Matrix n n L) (hdet : Y.det ≠ 0) :
    (Matrix n n (matrixGeneratedAlgebra (B := B) Y))ˣ :=
  (candidateMatrix_isUnit (B := B) Y hdet).unit

@[simp] theorem candidateMatrixUnit_val (Y : Matrix n n L) (hdet : Y.det ≠ 0) :
    (candidateMatrixUnit (B := B) Y hdet : Matrix n n (matrixGeneratedAlgebra (B := B) Y)) =
      candidateMatrix Y := IsUnit.unit_spec _

theorem candidateMatrixUnit_inv_det_coe (Y : Matrix n n L) (hdet : Y.det ≠ 0) :
    ((Matrix.det (↑((candidateMatrixUnit (B := B) Y hdet)⁻¹) :
      Matrix n n (matrixGeneratedAlgebra (B := B) Y)) : matrixGeneratedAlgebra (B := B) Y) : L) = Y.det⁻¹ := by
  apply mul_right_cancel₀ hdet
  rw [inv_mul_cancel₀ hdet]
  have h := congrArg (fun M : Matrix n n (matrixGeneratedAlgebra (B := B) Y) =>
    ((M.det : matrixGeneratedAlgebra (B := B) Y) : L))
    (Units.inv_mul (candidateMatrixUnit (B := B) Y hdet))
  simpa only [Matrix.det_mul, Subalgebra.coe_mul, Matrix.det_one, Subalgebra.coe_one,
    candidateMatrixUnit_val, candidateMatrix_det_coe] using h

def candidateKDerivation (dB : Derivation k B B) (dL : Derivation k L L)
    (Y : Matrix n n L) (A : Matrix n n B)
    (hbase : ∀ b, dL (algebraMap B L b) = algebraMap B L (dB b))
    (hode : ∀ i j, dL (Y i j) = ∑ l, algebraMap B L (A i l) * Y l j) :
    Derivation k (matrixGeneratedAlgebra (B := B) Y) (matrixGeneratedAlgebra (B := B) Y) where
  toFun x := ⟨dL x, matrixGeneratedAlgebra_stable
    (dB.restrictScalars ℤ) (dL.restrictScalars ℤ) Y A hbase hode x x.property⟩
  map_add' x y := Subtype.ext (dL.map_add (x : L) (y : L))
  map_smul' r x := Subtype.ext (dL.map_smul r (x : L))
  leibniz' x y := Subtype.ext (dL.leibniz (x : L) (y : L))
  map_one_eq_zero' := Subtype.ext dL.map_one_eq_zero

theorem candidateMatrixUnit_generates (Y : Matrix n n L) (hdet : Y.det ≠ 0) :
    Algebra.adjoin B
      (insert (Matrix.det (↑((candidateMatrixUnit (B := B) Y hdet)⁻¹) :
        Matrix n n (matrixGeneratedAlgebra (B := B) Y)))
        (Set.range (fun ij : n × n =>
          (candidateMatrixUnit (B := B) Y hdet : Matrix n n (matrixGeneratedAlgebra (B := B) Y)) ij.1 ij.2))) = ⊤ := by
  have hs : (insert (Matrix.det (↑((candidateMatrixUnit (B := B) Y hdet)⁻¹) :
        Matrix n n (matrixGeneratedAlgebra (B := B) Y)))
        (Set.range (fun ij : n × n =>
          (candidateMatrixUnit (B := B) Y hdet : Matrix n n (matrixGeneratedAlgebra (B := B) Y)) ij.1 ij.2))) =
      ((↑) : matrixGeneratedAlgebra (B := B) Y → L) ⁻¹'
        (insert Y.det⁻¹ (Set.range fun ij : n × n => Y ij.1 ij.2)) := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_range, Set.mem_preimage]
    constructor
    · rintro (rfl | ⟨ij,rfl⟩)
      · exact Or.inl (candidateMatrixUnit_inv_det_coe Y hdet)
      · exact Or.inr ⟨ij, by simp⟩
    · rintro (hx | ⟨ij,hij⟩)
      · left
        apply Subtype.ext
        exact hx.trans (candidateMatrixUnit_inv_det_coe Y hdet).symm
      · right
        refine ⟨ij, Subtype.ext ?_⟩
        simpa using hij
  rw [hs]
  exact Algebra.adjoin_adjoin_coe_preimage

theorem candidateKDerivation_base (dB : Derivation k B B) (dL : Derivation k L L)
    (Y : Matrix n n L) (A : Matrix n n B)
    (hbase : ∀ b, dL (algebraMap B L b) = algebraMap B L (dB b))
    (hode : ∀ i j, dL (Y i j) = ∑ l, algebraMap B L (A i l) * Y l j) (b : B) :
    candidateKDerivation dB dL Y A hbase hode
      (algebraMap B (matrixGeneratedAlgebra (B := B) Y) b) =
      algebraMap B (matrixGeneratedAlgebra (B := B) Y) (dB b) :=
  Subtype.ext (hbase b)

theorem candidateKDerivation_ode (dB : Derivation k B B) (dL : Derivation k L L)
    (Y : Matrix n n L) (A : Matrix n n B) (hdet : Y.det ≠ 0)
    (hbase : ∀ b, dL (algebraMap B L b) = algebraMap B L (dB b))
    (hode : ∀ i j, dL (Y i j) = ∑ l, algebraMap B L (A i l) * Y l j) :
    matrixDerivative (candidateKDerivation dB dL Y A hbase hode)
      (candidateMatrixUnit (B := B) Y hdet : Matrix n n (matrixGeneratedAlgebra (B := B) Y)) =
      (algebraMap B (matrixGeneratedAlgebra (B := B) Y)).mapMatrix A *
        (candidateMatrixUnit (B := B) Y hdet : Matrix n n (matrixGeneratedAlgebra (B := B) Y)) := by
  rw [candidateMatrixUnit_val]
  ext i j
  change dL (Y i j) = _
  simpa [Matrix.mul_apply] using hode i j

theorem candidateConstantMultiplication_surjective
    (dB : Derivation k B B) (dL : Derivation k L L)
    (Y : Matrix n n L) (A : Matrix n n B) (hdet : Y.det ≠ 0)
    (hbase : ∀ b, dL (algebraMap B L b) = algebraMap B L (dB b))
    (hode : ∀ i j, dL (Y i j) = ∑ l, algebraMap B L (A i l) * Y l j) :
    Function.Surjective (pvConstantMultiplication dB
      (candidateKDerivation dB dL Y A hbase hode)
      (candidateKDerivation_base dB dL Y A hbase hode)) := by
  exact pvConstantMultiplication_surjective dB _ _ A (candidateMatrixUnit Y hdet)
    (candidateKDerivation_ode dB dL Y A hdet hbase hode)
    (candidateMatrixUnit_generates Y hdet)

#print axioms candidateMatrixUnit
#print axioms candidateMatrixUnit_val
#print axioms candidateMatrixUnit_inv_det_coe
#print axioms candidateKDerivation
#print axioms candidateMatrixUnit_generates
#print axioms candidateKDerivation_base
#print axioms candidateKDerivation_ode
#print axioms candidateConstantMultiplication_surjective
end StrictEUnit
