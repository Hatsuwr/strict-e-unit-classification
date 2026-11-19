import Stage17ArithmeticFrameODE
import Stage15TwoSidedDeterminantClassification

/-! The actual arithmetic Euler frame supplies its original determinant's
nonvanishing off zero. Laurent clearing is constructed over the same subfield;
its actual entire identity is evaluated before applying the determinant ODE. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators
namespace StrictEUnit
local instance (k : Subfield ℂ) : AddGroup (subfieldEntireFunctionAlgebra k) :=
  @AddCommGroup.toAddGroup _
    (@Ring.toAddCommGroup _ (subfieldEntireFunctionAlgebra k).toRing)
local instance (k : Subfield ℂ) : CommRing (subfieldEntireFunctionAlgebra k) :=
  (subfieldEntireFunctionAlgebra k).toCommRing

/-- No strict-E or arithmetic-growth assumption is needed for this propagation:
the actual entire frame equation and one nonzero determinant suffice. -/
theorem stage23_arithmeticFrame_det_nonzero_off_origin
    (k : Subfield ℂ) {n : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix n n (LaurentPolynomial k)) (M : Matrix n n k)
    (F : Matrix n n (subfieldEntireFunctionAlgebra k))
    (hF : Stage17ActualEulerFrameRelation k B M F)
    (h1 : (F.map (stage14_subfieldEntireEvaluation k 1)).det ≠ 0) :
    ∀ z : ℂ, z ≠ 0 → (F.map (stage14_subfieldEntireEvaluation k z)).det ≠ 0 := by
  obtain ⟨L, hL, P, hP⟩ := stage16_laurentMatrix_exists_positive_clearing B
  let A : Matrix n n entireFunctionAlgebra :=
    fun i j => (Polynomial.aeval (subfieldEntireCoordinate k) (P i j)).val
  let C : Matrix n n entireFunctionAlgebra :=
    fun i j => (subfieldEntireCoordinate k ^ L *
      algebraMap k (subfieldEntireFunctionAlgebra k) (M i j)).val
  let G : Matrix n n entireFunctionAlgebra := fun i j => (F i j).val
  have hg : ∀ z : ℂ, z ≠ 0 → ∀ i j,
      (entireCoordinate^(L+1)).val z * deriv (G i j).val z =
        (∑ l, (A i l).val z * (G l j).val z) -
          ∑ l, (G i l).val z * (C l j).val z := by
    intro z hz i j
    have h := congrArg (stage14_subfieldEntireEvaluation k z)
      (stage17_actualEulerFrame_cleared k B M F hF L P hP i j)
    rw [map_sub (stage14_subfieldEntireEvaluation k z)] at h
    simp only [map_mul, map_pow, map_sum, AlgHom.commutes] at h
    change z^L * (z * deriv (F i j).val.val z) =
      (∑ l, (Polynomial.aeval (subfieldEntireCoordinate k) (P i l)).val.val z *
        (F l j).val.val z) -
      ∑ l, z^L * (F i l).val.val z * (M l j : ℂ) at h
    change z^(L+1) * deriv (F i j).val.val z =
      (∑ l, (Polynomial.aeval (subfieldEntireCoordinate k) (P i l)).val.val z *
        (F l j).val.val z) -
      ∑ l, (F i l).val.val z * (z^L * (M l j : ℂ))
    rw [pow_succ, mul_assoc, h]
    congr 1
    apply Finset.sum_congr rfl
    intro l hl
    ring
  have hp : ∀ z : ℂ, z ≠ 0 → (entireCoordinate^(L+1)).val z ≠ 0 :=
    fun z hz => pow_ne_zero _ hz
  exact entireMatrix_two_sided_determinant_nonzero_off_origin
    (entireCoordinate^(L+1)) A C G hg hp h1

end StrictEUnit
#print axioms StrictEUnit.stage23_arithmeticFrame_det_nonzero_off_origin
