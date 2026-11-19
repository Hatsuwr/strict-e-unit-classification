import PolynomialConnectionClearing
import MinimalDifferentialCompanion
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
The original clearing identity forces the sparse shift rows. Consequently,
the first row of the original polynomialConnectionSequence has the literal
scalar companion recurrence. No alternate matrix or scalar tuple is selected.
-/
noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

variable {K : Type*} [Field K]

/-- Non-last rows of the SAME U are forced by its original rational clearing
identity; no sparse-shape premise is added. -/
theorem cleared_companion_shift_row
    (n : ℕ) (c : Fin (n+1) → RatFunc K) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
      algebraMap (Polynomial K) (RatFunc K) T *
        minimalDerivativeCompanion (n+1) c i j)
    (i : Fin n) (j : Fin (n+1)) :
    U i.castSucc j = (Pi.single i.succ T : Fin (n+1) → Polynomial K) j := by
  classical
  apply RatFunc.algebraMap_injective K
  have hi : i.val+1<n+1 := by omega
  by_cases hj : j=i.succ
  · subst j
    simpa [minimalDerivativeCompanion, hi, Pi.single_apply] using
      hclear i.castSucc i.succ
  · have hval : j.val ≠ i.val+1 := by
      intro heq
      apply hj
      exact Fin.ext heq
    simpa [minimalDerivativeCompanion, hi, Pi.single_apply, hj, Ne.symm hj, hval] using
      hclear i.castSucc j

/-- Exact sparse right-row multiplication, keeping the actual last row of U.
The zero output coordinate has no predecessor, including size one. -/
theorem cleared_companion_row_product
    (n : ℕ) (c : Fin (n+1) → RatFunc K) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
      algebraMap (Polynomial K) (RatFunc K) T *
        minimalDerivativeCompanion (n+1) c i j)
    (x : Fin (n+1) → Polynomial K) :
    (∑ i, x i * U i 0) = x (Fin.last n)*U (Fin.last n) 0 ∧
    ∀ j : Fin n, (∑ i, x i * U i j.succ) =
      x j.castSucc*T + x (Fin.last n)*U (Fin.last n) j.succ := by
  classical
  constructor
  · rw [Fin.sum_univ_castSucc]
    simp only [cleared_companion_shift_row n c T U hclear]
    simp [Pi.single_apply, Fin.ext_iff]
  · intro j
    rw [Fin.sum_univ_castSucc]
    simp only [cleared_companion_shift_row n c T U hclear]
    simp [Pi.single_apply, Fin.succ_inj, eq_comm]

/-- This is the actual W_m=T^m A_m polynomial recursion, not a supplied
recurrence for a replacement family. Its scalar factorial normalization is
still exactly dividedPolynomialConnectionSequence T U m. -/
theorem polynomialConnectionSequence_companion_first_row
    (n : ℕ) (c : Fin (n+1) → RatFunc K) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
      algebraMap (Polynomial K) (RatFunc K) T *
        minimalDerivativeCompanion (n+1) c i j)
    (m : ℕ) :
    polynomialConnectionSequence T U (m+1) 0 0 =
      T*(polynomialConnectionSequence T U m 0 0).derivative -
        (m : Polynomial K)*T.derivative*polynomialConnectionSequence T U m 0 0 +
        polynomialConnectionSequence T U m 0 (Fin.last n)*U (Fin.last n) 0 ∧
    ∀ j : Fin n, polynomialConnectionSequence T U (m+1) 0 j.succ =
      T*(polynomialConnectionSequence T U m 0 j.succ).derivative -
        (m : Polynomial K)*T.derivative*polynomialConnectionSequence T U m 0 j.succ +
        (polynomialConnectionSequence T U m 0 j.castSucc*T +
          polynomialConnectionSequence T U m 0 (Fin.last n)*U (Fin.last n) j.succ) := by
  have hrow := cleared_companion_row_product n c T U hclear
    (fun i => polynomialConnectionSequence T U m 0 i)
  constructor
  · change T*(polynomialConnectionSequence T U m 0 0).derivative -
      (m : Polynomial K)*T.derivative*polynomialConnectionSequence T U m 0 0 +
      (∑ i, polynomialConnectionSequence T U m 0 i*U i 0) = _
    rw [hrow.1]
  · intro j
    change T*(polynomialConnectionSequence T U m 0 j.succ).derivative -
      (m : Polynomial K)*T.derivative*polynomialConnectionSequence T U m 0 j.succ +
      (∑ i, polynomialConnectionSequence T U m 0 i*U i j.succ) = _
    rw [hrow.2 j]

end StrictEUnit
end
