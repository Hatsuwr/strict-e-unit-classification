import CandidateFaithfullyFlat
import MatrixCandidateTorsorCriterion
import LaurentDerivativeConstants

/-! A general checked composition, not yet a construction for the wide system.
The base simplicity and exact ambient constants hypotheses remain explicit.
This comparison concerns the candidate's own tensor square, not its action
on the wide solution algebra. -/
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
section Generic
variable {k B L n : Type*} [Field k] [CommRing B] [Field L]
  [Algebra k B] [Algebra k L] [Algebra B L] [IsScalarTower k B L]
  [Fintype n] [DecidableEq n] [IsNoetherianRing B]

theorem v5_candidateConstantMultiplication_bijective_of_simple_base
    (dB : Derivation k B B) (dL : Derivation k L L)
    (Y : Matrix n n L) (A : Matrix n n B) (hdet : Y.det ≠ 0)
    (hb : ∀ b, dL (algebraMap B L b) = algebraMap B L (dB b))
    (hy : ∀ i j, dL (Y i j) = ∑ l, algebraMap B L (A i l) * Y l j)
    (hsimple : ∀ I : Ideal B, (∀ x ∈ I, dB x ∈ I) → I ≠ ⊥ → I = ⊤)
    (hconstants : ∀ a, dL a = 0 → ∃ c : k, algebraMap k L c = a) :
    Function.Bijective (pvConstantMultiplication dB
      (candidateKDerivation dB dL Y A hb hy)
      (candidateKDerivation_base dB dL Y A hb hy)) := by
  letI := matrixGeneratedAlgebra_faithfullyFlat dB dL Y A hdet hb hy hsimple
  exact candidateConstantMultiplication_bijective dB dL Y A hdet hb hy hconstants

end Generic

#print axioms v5_candidateConstantMultiplication_bijective_of_simple_base
end StrictEUnit
