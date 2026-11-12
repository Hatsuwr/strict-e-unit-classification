import ActualRationalClassBaseUnits

noncomputable section
open scoped Classical
namespace StrictEUnit
variable {K C : Type*} {I : C → Type*} {J : Type*}
  [Field K] [CharZero K] [Fintype C] [DecidableEq C]
  [∀ c, Fintype (I c)] [∀ c, DecidableEq (I c)] [Fintype J] [DecidableEq J]

def reindexedClassResidue (xi : C → K) (L : ∀ c, Matrix (I c) (I c) K)
    (e : (Σ c, I c) ≃ J) : Matrix J J K :=
  Matrix.reindexAlgEquiv K K e
    (Matrix.blockDiagonal' (fun c => Matrix.diagonal (fun _ => xi c) + L c))

def reindexedClassBaseUnit (m : C → ℤ) (L : ∀ c, Matrix (I c) (I c) K)
    (hL : ∀ c, IsNilpotent (L c)) (e : (Σ c, I c) ≃ J) :
    (Matrix J J (LaurentLogBase K))ˣ :=
  reindexedBlockUnit (fun c => fixedExponentBaseUnit (m c) (L c) (hL c)) e

theorem reindexedClassBaseUnit_equation
    (N : ℕ) (hN : N ≠ 0) (xi : C → K) (m : C → ℤ)
    (hm : ∀ c, (m c : K) / (N : K) = xi c)
    (L : ∀ c, Matrix (I c) (I c) K) (hL : ∀ c, IsNilpotent (L c))
    (e : (Σ c, I c) ≃ J) :
    matrixDerivative (manuscriptBaseDerivation N) (reindexedClassBaseUnit m L hL e).val =
      ramifiedConstantMatrix (reindexedClassResidue xi L e) *
        (reindexedClassBaseUnit m L hL e).val := by
  have hh := reindexedBlockUnit_equation (manuscriptBaseDerivation (k := K) N)
    (fun c => ramifiedConstantMatrix (Matrix.diagonal (fun _ : I c => xi c) + L c))
    (fun c => fixedExponentBaseUnit (m c) (L c) (hL c))
    (fun c => fixedExponentBaseUnit_equation N hN (m c) (xi c) (hm c) (L c) (hL c)) e
  have he : Matrix.reindexAlgEquiv (LaurentLogBase K) (LaurentLogBase K) e
      (Matrix.blockDiagonal' (fun c => ramifiedConstantMatrix
        (Matrix.diagonal (fun _ : I c => xi c) + L c))) =
      ramifiedConstantMatrix (reindexedClassResidue xi L e) := by
    apply Matrix.ext
    intro i j
    change Matrix.blockDiagonal' (fun c => ramifiedConstantMatrix
        (Matrix.diagonal (fun _ : I c => xi c) + L c)) (e.symm i) (e.symm j) =
      algebraMap K (LaurentLogBase K) (Matrix.blockDiagonal'
        (fun c => Matrix.diagonal (fun _ : I c => xi c) + L c) (e.symm i) (e.symm j))
    obtain ⟨c,a⟩ := e.symm i
    obtain ⟨b,d⟩ := e.symm j
    by_cases h : c = b
    · subst b
      simp [Matrix.blockDiagonal'_apply_eq, ramifiedConstantMatrix]
    · simp [Matrix.blockDiagonal'_apply_ne _ _ _ h]
  rw [he] at hh
  exact hh

end StrictEUnit
end
