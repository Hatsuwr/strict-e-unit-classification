import ReindexedBlockUnit
import FiniteLogBaseIdentification

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K C : Type*} {I : C → Type*} {J : Type*}
  [Field K] [Fintype C] [DecidableEq C] [∀ c, Fintype (I c)] [∀ c, DecidableEq (I c)]
  [Fintype J] [DecidableEq J]

theorem matrixDerivative_blockDiagonal
    (d : Derivation K (LaurentLogBase K) (LaurentLogBase K))
    (A : ∀ c, Matrix (I c) (I c) (LaurentLogBase K)) :
    matrixDerivative d (Matrix.blockDiagonal' A) =
      Matrix.blockDiagonal' (fun c => matrixDerivative d (A c)) := by
  ext ⟨c,i⟩ ⟨b,j⟩
  by_cases h : c = b
  · subst b
    simp [matrixDerivative, Matrix.blockDiagonal'_apply_eq]
  · simp [matrixDerivative, Matrix.blockDiagonal'_apply_ne _ _ _ h]

/-- Exact differential equation survives actual dependent block gluing and
reindexing to the original rank. -/
theorem reindexedBlockUnit_equation
    (d : Derivation K (LaurentLogBase K) (LaurentLogBase K))
    (M : ∀ c, Matrix (I c) (I c) (LaurentLogBase K))
    (Z : ∀ c, (Matrix (I c) (I c) (LaurentLogBase K))ˣ)
    (hZ : ∀ c, matrixDerivative d (Z c).val = M c * (Z c).val)
    (e : (Σ c, I c) ≃ J) :
    matrixDerivative d (reindexedBlockUnit Z e).val =
      (Matrix.reindexAlgEquiv (LaurentLogBase K) (LaurentLogBase K) e
        (Matrix.blockDiagonal' M)) * (reindexedBlockUnit Z e).val := by
  have hb : matrixDerivative d (finiteBlockUnit Z).val =
      Matrix.blockDiagonal' M * (finiteBlockUnit Z).val := by
    change matrixDerivative d (Matrix.blockDiagonal' (fun c => (Z c).val)) =
      Matrix.blockDiagonal' M * Matrix.blockDiagonal' (fun c => (Z c).val)
    rw [matrixDerivative_blockDiagonal]
    simp only [hZ, Matrix.blockDiagonal'_mul]
  change matrixDerivative d
      (Matrix.reindexAlgEquiv (LaurentLogBase K) (LaurentLogBase K) e (finiteBlockUnit Z).val) =
      (Matrix.reindexAlgEquiv (LaurentLogBase K) (LaurentLogBase K) e (Matrix.blockDiagonal' M)) *
      (Matrix.reindexAlgEquiv (LaurentLogBase K) (LaurentLogBase K) e (finiteBlockUnit Z).val)
  rw [← map_mul]
  rw [← hb]
  rfl

end StrictEUnit
end
