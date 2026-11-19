import PolynomialConnectionFaceRecurrence
import AttainedIrregularSlope
import ExpandedConnectionIntegrality
import ConstantCompanionArithmeticObstruction
import SameCompanionScalarTuple
import CompanionCommonDenominatorLocalBounds
import ReciprocalValuationDegree

/-! Source-only final local composition. Face/support dependencies are pending
validation at freeze. No local regularity or weighted recurrence is assumed. -/
noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

/-- The derived valuation inequalities are precisely the existing scalar
regular-singular predicate for the selected last-row tuple, including signs. -/
theorem sameCompanionScalarTuple_regular_of_common_denominators
    {K : Type*} [Field K] [NumberField K]
    (n : ℕ) (c : Fin (n+1) → RatFunc K) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (hT : T ≠ 0)
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
      algebraMap (Polynomial K) (RatFunc K) T * minimalDerivativeCompanion (n+1) c i j)
    (E : ℝ) (hE : 1 ≤ E)
    (hden : ∀ s : ℕ, ∃ d : ℕ, 0 < d ∧ (d:ℝ) ≤ E^(s+1) ∧
      ∀ m, m ≤ s → ∀ i j : Fin (n+1), ∀ l : ℕ,
        IsIntegral ℤ ((d:K)*(dividedPolynomialConnectionSequence T U m i j).coeff l)) :
    ReciprocalRegularSingularBounds (n+1)
      (sameCompanionScalarTuple (n+1) (Nat.succ_pos n) T U) := by
  have hb := companion_common_denominators_local_bounds n c T U hT hclear E hE hden
  intro i hi
  cases i using Fin.lastCases with
  | last => simp [sameCompanionScalarTuple]
  | cast i =>
    have hidx : (⟨n+1-1,by omega⟩ : Fin (n+1)) = Fin.last n := by
      apply Fin.ext
      simp
    have hne : U (Fin.last n) i ≠ 0 := by
      simpa only [sameCompanionScalarTuple, Fin.lastCases_castSucc, hidx, neg_ne_zero] using hi
    simpa only [sameCompanionScalarTuple, Fin.lastCases_last, Fin.lastCases_castSucc,
      hidx, Polynomial.natTrailingDegree_neg, Fin.coe_castSucc] using hb i hne

end StrictEUnit
end
