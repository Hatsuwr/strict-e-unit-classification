import DualBinomialOperator
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! SOURCE ONLY. Literal matrix attachment to the separately frozen operator
core. Its compiler acceptance is pending. Constant-field linearity only. -/
noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {k B : Type*} [Field k] [Field B] [Algebra k B]

/-- Coordinatewise ordinary derivative, linear only over k. -/
def matrixColumnDerivative (d : Derivation k B B) (r : ℕ) : Module.End k (Fin r → B) where
  toFun v i := d (v i)
  map_add' v w := by funext i; exact map_add d (v i) (w i)
  map_smul' c v := by funext i; exact d.map_smul c (v i)

/-- Literal left matrix action, restricted to the constant field. -/
def matrixColumnAction {r : ℕ} (A : Matrix (Fin r) (Fin r) B) :
    Module.End k (Fin r → B) := A.mulVecLin.restrictScalars k

def matrixDualColumn (d : Derivation k B B) {r : ℕ}
    (A : Matrix (Fin r) (Fin r) B) : Module.End k (Fin r → B) :=
  matrixColumnDerivative d r - matrixColumnAction A

/-- The literal normalized-system connection matrices, with right multiplication
by the original A in the recurrence. No matrix is supplied at higher orders. -/
def matrixConnectionSequence (d : Derivation k B B) {r : ℕ}
    (A : Matrix (Fin r) (Fin r) B) : ℕ → Matrix (Fin r) (Fin r) B
  | 0 => 1
  | n+1 => ((matrixConnectionSequence d A n).map (fun z => d z)) +
      matrixConnectionSequence d A n * A

theorem matrixColumnDerivative_mulVec (d : Derivation k B B) {r : ℕ}
    (C : Matrix (Fin r) (Fin r) B) (v : Fin r → B) :
    matrixColumnDerivative d r (C *ᵥ v) =
      (C.map (fun z => d z)) *ᵥ v + C *ᵥ matrixColumnDerivative d r v := by
  funext i
  change d (∑ j, C i j * v j) =
    (∑ j, d (C i j) * v j) + ∑ j, C i j * d (v j)
  simp only [map_sum, Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

/-- Exact intertwining identity from Leibniz, not B-linearity of D. -/
theorem matrix_dual_commutator (d : Derivation k B B) {r : ℕ}
    (A C : Matrix (Fin r) (Fin r) B) :
    matrixColumnDerivative d r * matrixColumnAction C -
      matrixColumnAction C * matrixDualColumn d A =
      matrixColumnAction ((C.map (fun z => d z)) + C*A) := by
  apply LinearMap.ext
  intro v
  change matrixColumnDerivative d r (C *ᵥ v) -
    C *ᵥ (matrixColumnDerivative d r v - A *ᵥ v) =
      ((C.map (fun z => d z)) + C*A) *ᵥ v
  rw [matrixColumnDerivative_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
    Matrix.add_mulVec]
  abel

/-- The operator tower is identified with the ORIGINAL recursively defined
matrix sequence, with the same derivative and same A. -/
theorem matrix_dual_tower (d : Derivation k B B) {r : ℕ}
    (A : Matrix (Fin r) (Fin r) B) (n : ℕ) :
    dualConnectionTower (matrixColumnDerivative d r) (matrixDualColumn d A) n =
      matrixColumnAction (matrixConnectionSequence d A n) := by
  induction n with
  | zero =>
    rw [dualConnectionTower_zero]
    apply LinearMap.ext
    intro v
    funext i
    change v i = ((1 : Matrix (Fin r) (Fin r) B) *ᵥ v) i
    rw [Matrix.one_mulVec]
  | succ n ih =>
    rw [dualConnectionTower_succ, ih, matrix_dual_commutator]
    rfl

theorem matrix_connection_raw_binomial (d : Derivation k B B) {r : ℕ}
    (A : Matrix (Fin r) (Fin r) B) (n : ℕ) (P : Fin r → B) :
    matrixConnectionSequence d A n *ᵥ P =
      ∑ h ∈ Finset.range (n+1),
        ((-1 : k)^h * (n.choose h : k)) •
          (((matrixColumnDerivative d r)^(n-h)) (((matrixDualColumn d A)^h) P)) := by
  have he := dualConnectionTower_binomial
    (matrixColumnDerivative d r) (matrixDualColumn d A) n P
  rw [matrix_dual_tower] at he
  exact he

section Divided
variable [CharZero k]

theorem matrix_connection_divided_binomial (d : Derivation k B B) {r : ℕ}
    (A : Matrix (Fin r) (Fin r) B) (n : ℕ) (P : Fin r → B) :
    (n.factorial : k)⁻¹ • (matrixConnectionSequence d A n *ᵥ P) =
      ∑ h ∈ Finset.range (n+1),
        ((-1 : k)^h / ((n-h).factorial : k)) •
          (((matrixColumnDerivative d r)^(n-h))
            (dualDividedColumn (matrixDualColumn d A) P h)) := by
  have he := dualConnectionTower_divided
    (matrixColumnDerivative d r) (matrixDualColumn d A) n P
  rw [matrix_dual_tower] at he
  exact he

theorem matrix_connection_divided_shifted (d : Derivation k B B) {r : ℕ}
    (A : Matrix (Fin r) (Fin r) B) (n j : ℕ) (P : Fin r → B) :
    (n.factorial : k)⁻¹ •
      (matrixConnectionSequence d A n *ᵥ dualDividedColumn (matrixDualColumn d A) P j) =
      ∑ h ∈ Finset.range (n+1),
        (((-1 : k)^h * ((j+h).choose h : k)) / ((n-h).factorial : k)) •
          (((matrixColumnDerivative d r)^(n-h))
            (dualDividedColumn (matrixDualColumn d A) P (j+h))) := by
  have he := dualConnectionTower_divided_shifted
    (matrixColumnDerivative d r) (matrixDualColumn d A) n j P
  rw [matrix_dual_tower] at he
  exact he

end Divided
end StrictEUnit
end
