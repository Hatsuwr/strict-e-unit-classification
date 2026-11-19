import EulerForcingCoordinateOrder

noncomputable section
open scoped BigOperators Classical Matrix
namespace StrictEUnit
variable {K : Type*} [Field K]

/-- The actual shifted source block has the required one-step support and
unit superdiagonal. No conditions on its final row are added. -/
theorem augmentedSourceEulerBase_cyclicShape (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) :
    EulerCyclicShape (augmentedSourceEulerBase n T U) := by
  constructor
  · intro i j hij
    cases i using Fin.lastCases with
    | last =>simp only [Fin.val_last] at hij;omega
    | cast i =>
      have h1 : j≠i.succ := by intro h;subst j;simp at hij
      have h2 : i.castSucc≠j := by intro h;subst j;simp at hij
      simp [augmentedSourceEulerBase,sameCompanionEulerPowerSeriesMatrix,
        Matrix.add_apply,Matrix.diagonal_apply,Pi.single_apply,h1,h1.symm,h2]
  · intro i j hij
    cases i using Fin.lastCases with
    | last =>simp only [Fin.val_last] at hij;omega
    | cast i =>
      have hj : j=i.succ := Fin.ext hij
      subst j
      have h2 : i.castSucc≠i.succ := by intro h;have := congrArg Fin.val h;simp at this
      simp [augmentedSourceEulerBase,sameCompanionEulerPowerSeriesMatrix,
        Matrix.add_apply,Matrix.diagonal_apply,Pi.single_apply,h2]

/-- The only new pivot is the inverse of the ACTUAL unit tail of T. -/
theorem augmentedSourceEulerColumn_unit (n : ℕ) (T : Polynomial K) (hT : T≠0)
    (i : Fin (n+1)) (hi : i.val+1=n+1) : IsUnit (augmentedSourceEulerColumn n T i) := by
  rw [augmentedSourceEulerColumn,if_pos hi]
  exact isUnit_of_mul_eq_one _ _ (PowerSeries.inv_mul_cancel _
    (sameCompanionEulerDenominatorSeries_constantCoeff_ne_zero T hT))

/-- All finite forcing extensions preserve the concrete cyclic shape. -/
theorem orderedForcingEulerMatrix_cyclicShape {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (g : Fin r →PowerSeries K) (u : ℕ)
    (hC : EulerCyclicShape C)
    (hg0 : ∀ i,i.val+1<r →g i=0) (hg1 : ∀ i,i.val+1=r →IsUnit (g i)) (d : ℕ) :
    EulerCyclicShape (orderedForcingEulerMatrix C g u d) := by
  induction d with
  | zero =>exact appendEulerBlock_cyclicShape C g _ hC hg0 hg1
  | succ d ih =>
    apply appendEulerBlock_cyclicShape _ _ _ ih
    · intro i hi;simp [show i.val+1≠(r+1)+d by omega]
    · intro i hi;simp [hi]

/-- The original augmented source matrix, after the explicit proved coordinate
permutation, has unit pivots and exactly the support needed for scalar jets. -/
theorem augmentedSourceEulerMatrix_ordered_cyclicShape (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T≠0) (d : ℕ) :
    EulerCyclicShape ((augmentedSourceEulerMatrix n T U d).submatrix
      (forcingCoordinateEquiv (n+1) d) (forcingCoordinateEquiv (n+1) d)) := by
  rw [augmentedSourceEulerMatrix,polynomialForcingEulerMatrix_ordered]
  apply orderedForcingEulerMatrix_cyclicShape
  · exact augmentedSourceEulerBase_cyclicShape n T U
  · intro i hi;rw [augmentedSourceEulerColumn,if_neg (by omega)]
  · exact augmentedSourceEulerColumn_unit n T hT

end StrictEUnit
end
