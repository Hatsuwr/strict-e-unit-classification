import UnitMinorExtraction
import Mathlib.RingTheory.Ideal.Maps

/-! Determinantal ideals commute with arbitrary commutative-ring base change. -/
noncomputable section
namespace StrictEUnit
variable {B S m n : Type*} [CommRing B] [CommRing S]

/-- Determinants, including the full generating sets of minors, commute with ring maps. -/
theorem matrixMinorIdeal_map (f : B →+* S) (r : ℕ) (M : Matrix m n B) :
    Ideal.map f (matrixMinorIdeal r M) = matrixMinorIdeal r (M.map f) := by
  classical
  unfold matrixMinorIdeal
  rw [Ideal.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨u,v,rfl⟩, rfl⟩
    refine ⟨u,v,?_⟩
    exact f.map_det _
  · rintro ⟨u,v,rfl⟩
    exact ⟨(M.submatrix u v).det, ⟨u,v,rfl⟩, f.map_det _⟩

/-- The zero/unit pair of neighboring determinantal ideals survives every ring map. -/
theorem matrixMinorIdeal_map_rank (f : B →+* S) (r : ℕ) (M : Matrix m n B)
    (ht : matrixMinorIdeal r M = ⊤) (hz : matrixMinorIdeal (r+1) M = ⊥) :
    matrixMinorIdeal r (M.map f) = ⊤ ∧ matrixMinorIdeal (r+1) (M.map f) = ⊥ := by
  rw [← matrixMinorIdeal_map f r M, ← matrixMinorIdeal_map f (r+1) M, ht, hz]
  simp [Ideal.map_top]

/-- In particular every local target ring has a projective base-changed matrix cokernel. -/
theorem matrixCokernel_projective_baseChange [Fintype m] [Fintype n] [IsLocalRing S]
    (f : B →+* S) (r : ℕ) (M : Matrix m n B)
    (ht : matrixMinorIdeal r M = ⊤) (hz : matrixMinorIdeal (r+1) M = ⊥) :
    Module.Projective S ((m → S) ⧸ LinearMap.range (M.map f).mulVecLin) := by
  obtain ⟨ht',hz'⟩ := matrixMinorIdeal_map_rank f r M ht hz
  exact matrixCokernel_projective_of_minorIdeals r (M.map f) ht' hz'
end StrictEUnit
#print axioms StrictEUnit.matrixMinorIdeal_map
#print axioms StrictEUnit.matrixMinorIdeal_map_rank
#print axioms StrictEUnit.matrixCokernel_projective_baseChange
