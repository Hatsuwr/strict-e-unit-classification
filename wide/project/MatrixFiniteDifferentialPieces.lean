import DifferentialFiniteFiltration

/-! Finite differential pieces using entries of a fundamental matrix and its
inverse. This proves finite generation and stability, not projectivity. -/
noncomputable section
namespace StrictEUnit
variable {k B R n : Type*} [CommRing k] [CommRing B] [CommRing R]
 [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
 [Fintype n] [DecidableEq n]

theorem fundamental_matrix_inverse_ode (d : Derivation k R R)
    (A : Matrix n n R) (Y : (Matrix n n R)ˣ)
    (hy : matrixDerivative d (Y : Matrix n n R) = A * (Y : Matrix n n R)) :
    matrixDerivative d (↑Y⁻¹ : Matrix n n R) = -(↑Y⁻¹ : Matrix n n R) * A := by
  have h := matrixDerivative_mul d (Y : Matrix n n R) (↑Y⁻¹ : Matrix n n R)
  rw [Units.mul_inv, matrixDerivative_one, hy, mul_assoc, Units.mul_inv, mul_one] at h
  apply Y.isUnit.mul_left_cancel
  rw [neg_mul, mul_neg, ← mul_assoc, Units.mul_inv, one_mul]
  exact eq_neg_of_add_eq_zero_right h.symm

def matrixDifferentialGenerators (Y : (Matrix n n R)ˣ) : Set R :=
  Set.range (fun ij : n × n => (Y : Matrix n n R) ij.1 ij.2) ∪
  Set.range (fun ij : n × n => (↑Y⁻¹ : Matrix n n R) ij.1 ij.2)

theorem matrixDifferentialGenerators_finite (Y : (Matrix n n R)ˣ) :
    (matrixDifferentialGenerators Y).Finite :=
  (Set.finite_range _).union (Set.finite_range _)

theorem matrixDifferentialGenerators_stable (d : Derivation k R R)
    (A : Matrix n n B) (Y : (Matrix n n R)ˣ)
    (hy : matrixDerivative d (Y : Matrix n n R) =
      (algebraMap B R).mapMatrix A * (Y : Matrix n n R)) :
    ∀ x ∈ matrixDifferentialGenerators Y,
      d x ∈ Submodule.span B (insert 1 (matrixDifferentialGenerators Y)) := by
  intro x hx
  rcases hx with ⟨⟨i,j⟩,rfl⟩ | ⟨⟨i,j⟩,rfl⟩
  · have h := congrArg (fun M : Matrix n n R => M i j) hy
    simp only [matrixDerivative_apply] at h
    rw [h]
    simp only [Matrix.mul_apply, Matrix.neg_apply]
    apply Submodule.sum_mem
    intro l hl
    simpa [Algebra.smul_def] using
      (Submodule.span B (insert 1 (matrixDifferentialGenerators Y))).smul_mem (A i l)
        (Submodule.subset_span (Set.mem_insert_of_mem _ (Or.inl ⟨(l,j),rfl⟩)))
  · have h := congrArg (fun M : Matrix n n R => M i j)
      (fundamental_matrix_inverse_ode d _ Y hy)
    simp only [matrixDerivative_apply] at h
    rw [h]
    simp only [Matrix.mul_apply, Matrix.neg_apply]
    apply Submodule.sum_mem
    intro l hl
    simpa [Algebra.smul_def, mul_comm] using
      (Submodule.span B (insert 1 (matrixDifferentialGenerators Y))).smul_mem (-(A l j))
        (Submodule.subset_span (Set.mem_insert_of_mem _ (Or.inr ⟨(i,l),rfl⟩)))

theorem matrixInverseEntries_generate (Y : (Matrix n n R)ˣ)
    (hgen : Algebra.adjoin B (insert (Matrix.det (↑Y⁻¹ : Matrix n n R))
      (Set.range fun ij : n × n => (Y : Matrix n n R) ij.1 ij.2)) = ⊤) :
    Algebra.adjoin B (matrixDifferentialGenerators Y) = ⊤ := by
  apply top_unique
  rw [← hgen]
  apply Algebra.adjoin_le
  intro x hx
  rcases hx with rfl | ⟨ij,rfl⟩
  · apply matrix_det_mem_subalgebra
    intro i j
    exact Algebra.subset_adjoin (Or.inr ⟨(i,j),rfl⟩)
  · exact Algebra.subset_adjoin (Or.inl ⟨ij,rfl⟩)

theorem matrix_finite_differential_pieces
    (dB : Derivation k B B) (d : Derivation k R R)
    (hb : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
    (A : Matrix n n B) (Y : (Matrix n n R)ˣ)
    (hy : matrixDerivative d (Y : Matrix n n R) =
      (algebraMap B R).mapMatrix A * (Y : Matrix n n R))
    (hgen : Algebra.adjoin B (matrixDifferentialGenerators Y) = ⊤)
    (t : Set R) (ht : t.Finite) :
    ∃ m, (differentialPiece (B := B) (matrixDifferentialGenerators Y) m).FG ∧
      t ⊆ differentialPiece (B := B) (matrixDifferentialGenerators Y) m ∧
      ∀ x ∈ differentialPiece (B := B) (matrixDifferentialGenerators Y) m,
        d x ∈ differentialPiece (B := B) (matrixDifferentialGenerators Y) m := by
  obtain ⟨m,hm⟩ := finite_mem_some_differentialPiece (matrixDifferentialGenerators Y) t ht
    (by rw [hgen]; exact Set.subset_univ _)
  exact ⟨m, differentialPiece_fg _ (matrixDifferentialGenerators_finite Y) m, hm,
    differentialPiece_stable dB d hb _ (matrixDifferentialGenerators_stable d A Y hy) m⟩

section Candidate
variable {L : Type*} [Field L] [Algebra k L] [Algebra B L] [IsScalarTower k B L]

theorem candidate_finite_differential_pieces
    (dB : Derivation k B B) (dL : Derivation k L L)
    (Y : Matrix n n L) (A : Matrix n n B) (hdet : Y.det ≠ 0)
    (hb : ∀ b, dL (algebraMap B L b) = algebraMap B L (dB b))
    (hy : ∀ i j, dL (Y i j) = ∑ l, algebraMap B L (A i l) * Y l j)
    (t : Set (matrixGeneratedAlgebra (B := B) Y)) (ht : t.Finite) :
    ∃ M : Submodule B (matrixGeneratedAlgebra (B := B) Y), M.FG ∧ t ⊆ M ∧
      ∀ x ∈ M, candidateKDerivation dB dL Y A hb hy x ∈ M := by
  obtain ⟨m,hfg,htm,hd⟩ := matrix_finite_differential_pieces dB
    (candidateKDerivation dB dL Y A hb hy) (candidateKDerivation_base dB dL Y A hb hy)
    A (candidateMatrixUnit Y hdet) (candidateKDerivation_ode dB dL Y A hdet hb hy)
    (matrixInverseEntries_generate _ (candidateMatrixUnit_generates Y hdet)) t ht
  exact ⟨_,hfg,htm,hd⟩
end Candidate

#print axioms fundamental_matrix_inverse_ode
#print axioms matrixDifferentialGenerators
#print axioms matrixDifferentialGenerators_finite
#print axioms matrixDifferentialGenerators_stable
#print axioms matrixInverseEntries_generate
#print axioms matrix_finite_differential_pieces
#print axioms candidate_finite_differential_pieces
end StrictEUnit
