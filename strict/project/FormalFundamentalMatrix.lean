import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Lean.Elab.Tactic.Omega

/-!
NEW SOURCE-ONLY: the ordinary formal fundamental matrix of an arbitrary
power-series matrix. Its coefficients are constructed recursively, starting
at the identity. All products are actual matrix products with A on the LEFT.
No solution, invertibility, convergence, or differential-field premise is used.
-/
noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

variable {K : Type*} [Field K] {r : ℕ}

/-- Coefficient recurrence W_0=I and
W_(n+1)=(n+1)^(-1) sum_(k=0)^n A_k W_(n-k).
The recursive index is strictly smaller, including k=0. -/
def formalFundamentalCoeff (A : Matrix (Fin r) (Fin r) (PowerSeries K)) :
    ℕ → Matrix (Fin r) (Fin r) K
  | 0 => 1
  | n+1 => ((n+1 : K)⁻¹) • ∑ k : Fin (n+1),
      A.map (PowerSeries.coeff K k.val) * formalFundamentalCoeff A (n-k.val)
termination_by n => n
decreasing_by omega

@[simp] theorem formalFundamentalCoeff_zero
    (A : Matrix (Fin r) (Fin r) (PowerSeries K)) :
    formalFundamentalCoeff A 0 = 1 := by
  rw [formalFundamentalCoeff]

theorem formalFundamentalCoeff_succ
    (A : Matrix (Fin r) (Fin r) (PowerSeries K)) (n : ℕ) :
    formalFundamentalCoeff A (n+1) = ((n+1 : K)⁻¹) •
      ∑ k : Fin (n+1),
        A.map (PowerSeries.coeff K k.val) * formalFundamentalCoeff A (n-k.val) := by
  rw [formalFundamentalCoeff]

/-- The literal matrix whose entries have the recursively constructed
coefficients. No separate or chosen family of solutions is substituted. -/
def formalFundamentalMatrix (A : Matrix (Fin r) (Fin r) (PowerSeries K)) :
    Matrix (Fin r) (Fin r) (PowerSeries K) :=
  Matrix.of fun i j => PowerSeries.mk (fun n => formalFundamentalCoeff A n i j)

@[simp] theorem formalFundamentalMatrix_coeff
    (A : Matrix (Fin r) (Fin r) (PowerSeries K)) (n : ℕ) (i j : Fin r) :
    PowerSeries.coeff K n (formalFundamentalMatrix A i j) =
      formalFundamentalCoeff A n i j := by
  exact PowerSeries.coeff_mk (R := K) n (fun m => formalFundamentalCoeff A m i j)

/-- Exact coefficient convolution for an actual matrix product, not pointwise
multiplication of the underlying functions. -/
theorem powerSeries_matrix_mul_coeff
    (A B : Matrix (Fin r) (Fin r) (PowerSeries K)) (n : ℕ) (i j : Fin r) :
    PowerSeries.coeff K n ((A * B) i j) =
      ∑ k : Fin (n+1), ∑ l : Fin r,
        PowerSeries.coeff K k.val (A i l) *
          PowerSeries.coeff K (n-k.val) (B l j) := by
  rw [Matrix.mul_apply, map_sum]
  simp only [PowerSeries.coeff_mul]
  rw [Finset.sum_comm]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b : ℕ => ∑ l : Fin r,
      PowerSeries.coeff K a (A i l) * PowerSeries.coeff K b (B l j)) n]
  exact (Fin.sum_univ_eq_sum_range
    (fun k : ℕ => ∑ l : Fin r,
      PowerSeries.coeff K k (A i l) * PowerSeries.coeff K (n-k) (B l j))
    (n+1)).symm

/-- Evaluation at zero is exactly the identity, including the empty matrix. -/
theorem formalFundamentalMatrix_constantCoeff
    (A : Matrix (Fin r) (Fin r) (PowerSeries K)) :
    (formalFundamentalMatrix A).map (PowerSeries.constantCoeff K) = 1 := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.map_apply, formalFundamentalMatrix, Matrix.of_apply,
    PowerSeries.constantCoeff_mk, formalFundamentalCoeff_zero]

/-- The coefficient recurrence after cancelling the genuine nonzero integer
n+1 in the characteristic-zero coefficient field. -/
theorem formalFundamentalCoeff_succ_mul [CharZero K]
    (A : Matrix (Fin r) (Fin r) (PowerSeries K)) (n : ℕ) (i j : Fin r) :
    formalFundamentalCoeff A (n+1) i j * (n+1 : K) =
      ∑ k : Fin (n+1), ∑ l : Fin r,
        PowerSeries.coeff K k.val (A i l) * formalFundamentalCoeff A (n-k.val) l j := by
  have hnNat : ((n+1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have hn : (n+1 : K) ≠ 0 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hnNat
  rw [formalFundamentalCoeff_succ, Matrix.smul_apply, smul_eq_mul,
    mul_right_comm, inv_mul_cancel₀ hn, one_mul]
  exact Matrix.sum_apply i j Finset.univ
    (fun k : Fin (n+1) =>
      A.map (PowerSeries.coeff K k.val) * formalFundamentalCoeff A (n-k.val))

/-- The SAME constructed matrix satisfies the literal ordinary equation
W'=A W, with the derivative applied entrywise by Matrix.map. -/
theorem formalFundamentalMatrix_derivative [CharZero K]
    (A : Matrix (Fin r) (Fin r) (PowerSeries K)) :
    (formalFundamentalMatrix A).map (PowerSeries.derivative K) =
      A * formalFundamentalMatrix A := by
  apply Matrix.ext
  intro i j
  apply PowerSeries.ext
  intro n
  rw [Matrix.map_apply, PowerSeries.coeff_derivative,
    formalFundamentalMatrix_coeff, formalFundamentalCoeff_succ_mul,
    powerSeries_matrix_mul_coeff]
  simp only [formalFundamentalMatrix_coeff]

end StrictEUnit
end
