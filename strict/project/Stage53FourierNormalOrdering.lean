import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! RECOVERED SOURCE EXCERPT ONLY, UNCHECKED IN THE REPLACEMENT WORKSPACE.
The two declaration texts below were retained verbatim in the review thread.
This is newly scoped excerpt source, not a recovery of the complete Stage53 module.
The historical complete-file SHA256 is not claimed for this excerpt. -/
noncomputable section
open scoped BigOperators
open Finset
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Normal-ordered coefficient for the convention X ↦ -∂, ∂ ↦ X.
The filter is precisely the requested restriction j ≥ l. -/
def stage53_fourierCoeff {μ ν : ℕ} (a : Fin (μ+1) → Fin (ν+1) → K)
    (l : Fin (ν+1)) : Polynomial K :=
  ∑ i, ∑ j with l.val ≤ j.val,
    Polynomial.C ((-1)^j.val * a i j * (j.val.choose l.val : K)) *
      Polynomial.derivative^[j.val-l.val] (Polynomial.X^i.val)

/-- Terms below the diagonal vanish by the binomial coefficient. -/
theorem stage53_fourierCoeff_eq_unfiltered {μ ν : ℕ}
    (a : Fin (μ+1) → Fin (ν+1) → K) (l : Fin (ν+1)) :
    stage53_fourierCoeff a l = ∑ i, ∑ j,
      Polynomial.C ((-1)^j.val * a i j * (j.val.choose l.val : K)) *
        Polynomial.derivative^[j.val-l.val] (Polynomial.X^i.val) := by
  unfold stage53_fourierCoeff
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs with h
  · rfl
  · simp [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge h)]

end StrictEUnit
end
