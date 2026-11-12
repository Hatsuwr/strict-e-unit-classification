import Mathlib.Data.Fin.Basic

/-!
NEW MINIMAL FINITE-FUCHS DEPENDENCY, SOURCE ONLY AND UNRUN.
This is a new definition, not byte restoration of the lost Stage56 module.
Equivalence to the lost original Stage56 definition has NOT been proved.
The condition below is the concrete coefficient-vanishing premise required
by the retained focused normalization proofs. The top-column consequence
is proved directly from that premise. No arithmetic Fuchs theorem is asserted.
The historical module basename is used only to resolve the unchanged import
in the exact recovered prefix; this is not full Stage56 module acceptance.
-/
namespace StrictEUnit
variable {K : Type*} [Zero K]

/-- The concrete finite coefficient-vanishing hypothesis used by this NEW module. -/
def Stage56FiniteFuchs {μ ν : ℕ}
    (a : Fin (μ+1) → Fin (ν+1) → K) : Prop :=
  ∀ i j, ν + i.val < j.val + μ → a i j = 0

/-- Entries strictly left of the corner in the last column vanish under the premise. -/
theorem stage56_fuchs_topColumn {μ ν : ℕ}
    (a : Fin (μ+1) → Fin (ν+1) → K)
    (hf : Stage56FiniteFuchs a) (i : Fin (μ+1))
    (hiμ : i.val < μ) : a i (Fin.last ν) = 0 := by
  apply hf i (Fin.last ν)
  simpa only [Fin.val_last] using Nat.add_lt_add_left hiμ ν

end StrictEUnit
