import Stage24CommonFrameValueCoverage
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

/-! Binary block diagonals preserve actual minimal-polynomial rational spectrum.
This is an algebraic construction, not an arithmetic normal-form existence theorem. -/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

variable {k n m r : Type*} [Field k] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

/-- The actual block-diagonal algebra homomorphism from a pair of matrix algebras. -/
def stage27_blockDiagonalAlgHom :
    (Matrix n n k × Matrix m m k) →ₐ[k] Matrix (n ⊕ m) (n ⊕ m) k where
  toFun x := Matrix.fromBlocks x.1 0 0 x.2
  map_one' := Matrix.fromBlocks_one
  map_mul' x y := by
    simp only [Prod.fst_mul, Prod.snd_mul, Matrix.fromBlocks_multiply,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  map_zero' := Matrix.fromBlocks_zero
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Matrix.fromBlocks_add, add_zero]
  commutes' a := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal]

/-- A product of the two actual minimal polynomials annihilates the block matrix. -/
theorem stage27_blockDiagonal_aeval_minpoly_product
    (A : Matrix n n k) (B : Matrix m m k) :
    Polynomial.aeval (Matrix.fromBlocks A 0 0 B) (minpoly k A * minpoly k B) = 0 := by
  let φ := stage27_blockDiagonalAlgHom (k := k) (n := n) (m := m)
  change Polynomial.aeval (φ (A, B)) _ = 0
  rw [Polynomial.aeval_algHom_apply]
  have h : Polynomial.aeval (A, B) (minpoly k A * minpoly k B) = 0 := by
    rw [Polynomial.aeval_prod_apply]
    simp only [map_mul, minpoly.aeval, zero_mul, mul_zero, Prod.zero_eq_mk]
  rw [h, map_zero]

/-- Every minimal-polynomial root of the block matrix is already a root of
one of the two supplied matrices. No splitting or algebraic closedness is needed. -/
theorem stage27_blockDiagonal_minpoly_root
    (A : Matrix n n k) (B : Matrix m m k) (a : k)
    (ha : (minpoly k (Matrix.fromBlocks A 0 0 B)).IsRoot a) :
    (minpoly k A).IsRoot a ∨ (minpoly k B).IsRoot a := by
  have h := ha.dvd (minpoly.dvd k (Matrix.fromBlocks A 0 0 B)
    (stage27_blockDiagonal_aeval_minpoly_product A B))
  simpa only [Polynomial.IsRoot, Polynomial.eval_mul, mul_eq_zero] using h

/-- Rational minimal-polynomial spectra are preserved by the actual block sum. -/
theorem stage27_blockDiagonal_rational_spectrum [CharZero k]
    (A : Matrix n n k) (B : Matrix m m k)
    (hA : ∀ a : k, (minpoly k A).IsRoot a → ∃ q : ℚ, (q : k) = a)
    (hB : ∀ a : k, (minpoly k B).IsRoot a → ∃ q : ℚ, (q : k) = a) :
    ∀ a : k, (minpoly k (Matrix.fromBlocks A 0 0 B)).IsRoot a →
      ∃ q : ℚ, (q : k) = a := by
  intro a ha
  exact (stage27_blockDiagonal_minpoly_root A B a ha).elim (hA a) (hB a)

/-- Reindexing preserves the exact minimal polynomial, not just its roots. -/
theorem stage27_reindex_minpoly [Fintype r] [DecidableEq r]
    (e : n ≃ r) (A : Matrix n n k) :
    minpoly k (Matrix.reindex e e A) = minpoly k A :=
  minpoly.algEquiv_eq (Matrix.reindexAlgEquiv k k e) A

end StrictEUnit
