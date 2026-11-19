import TensorDerivation
import Mathlib.Data.Matrix.Basic

/-! Transition matrices between fundamental solutions of one differential
system are constant. Matrices are actual units, avoiding an assumed inverse
formula or an assumed product rule. This is not a PV existence theorem. -/
noncomputable section
namespace StrictEUnit
variable {k R n : Type*} [CommRing k] [CommRing R] [Algebra k R]
  [Fintype n] [DecidableEq n]

/-- Entrywise application of the actual coefficient derivation. -/
def matrixDerivative (δ : Derivation k R R) :
    Matrix n n R →ₗ[k] Matrix n n R where
  toFun M i j := δ (M i j)
  map_add' M N := by ext i j; exact map_add δ _ _
  map_smul' a M := by ext i j; exact map_smul δ.toLinearMap a _

omit [Fintype n] [DecidableEq n] in
@[simp] theorem matrixDerivative_apply (δ : Derivation k R R)
    (M : Matrix n n R) (i j : n) : matrixDerivative δ M i j = δ (M i j) := rfl

omit [DecidableEq n] in
/-- The product rule is proved using finite matrix multiplication sums. -/
theorem matrixDerivative_mul (δ : Derivation k R R) (M N : Matrix n n R) :
    matrixDerivative δ (M * N) =
      matrixDerivative δ M * N + M * matrixDerivative δ N := by
  ext i j
  simp only [matrixDerivative_apply, Matrix.mul_apply, map_sum,
    Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib, Matrix.add_apply]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  exact mul_comm _ _

omit [Fintype n] in
@[simp] theorem matrixDerivative_one (δ : Derivation k R R) :
    matrixDerivative δ (1 : Matrix n n R) = 0 := by
  ext i j
  by_cases h : i = j
  · subst j; simp [matrixDerivative_apply]
  · simp [matrixDerivative_apply, Matrix.one_apply, h]

/-- If Y is an invertible fundamental matrix and Z is any solution matrix,
then Y inverse times Z has constant entries. Invertibility of Z is not
needed, so the result applies in particular to two fundamental matrices. -/
theorem fundamental_matrix_transition_constant
    (δ : Derivation k R R) (A : Matrix n n R)
    (Y : (Matrix n n R)ˣ) (Z : Matrix n n R)
    (hY : matrixDerivative δ (Y : Matrix n n R) = A * (Y : Matrix n n R))
    (hZ : matrixDerivative δ Z = A * Z) :
    matrixDerivative δ ((↑Y⁻¹ : Matrix n n R) * Z) = 0 := by
  let T : Matrix n n R := (↑Y⁻¹ : Matrix n n R) * Z
  have hprod : (Y : Matrix n n R) * T = Z := by
    dsimp [T]
    rw [← mul_assoc, Units.mul_inv, one_mul]
  have hd := matrixDerivative_mul δ (Y : Matrix n n R) T
  rw [hprod, hZ, hY, mul_assoc, hprod] at hd
  have hz : (Y : Matrix n n R) * matrixDerivative δ T = 0 :=
    add_eq_left.mp hd.symm
  apply Y.isUnit.mul_left_cancel
  simpa only [mul_zero] using hz

/-- Entrywise form of the transition-constant conclusion. -/
theorem fundamental_matrix_transition_entry_constant
    (δ : Derivation k R R) (A : Matrix n n R)
    (Y Z : (Matrix n n R)ˣ)
    (hY : matrixDerivative δ (Y : Matrix n n R) = A * (Y : Matrix n n R))
    (hZ : matrixDerivative δ (Z : Matrix n n R) = A * (Z : Matrix n n R))
    (i j : n) :
    δ (((↑Y⁻¹ : Matrix n n R) * (Z : Matrix n n R)) i j) = 0 :=
  congrArg (fun M : Matrix n n R => M i j)
    (fundamental_matrix_transition_constant δ A Y (Z : Matrix n n R) hY hZ)
end StrictEUnit

#print axioms StrictEUnit.matrixDerivative
#print axioms StrictEUnit.matrixDerivative_apply
#print axioms StrictEUnit.matrixDerivative_mul
#print axioms StrictEUnit.matrixDerivative_one
#print axioms StrictEUnit.fundamental_matrix_transition_constant
#print axioms StrictEUnit.fundamental_matrix_transition_entry_constant
