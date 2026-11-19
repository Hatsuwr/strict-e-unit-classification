import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Matrix.Basic
import Lean.Elab.Tactic.Omega

noncomputable section
namespace StrictEUnit

/-- The last row of the SAME clearing, followed by its leading coefficient. -/
def sameCompanionScalarTuple {K : Type*} [Field K] (r : ℕ) (hr : 0 < r)
    (T : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K)) :
    Fin (r+1) → Polynomial K :=
  Fin.lastCases T (fun i => -U ⟨r-1, by omega⟩ i)

end StrictEUnit
end
