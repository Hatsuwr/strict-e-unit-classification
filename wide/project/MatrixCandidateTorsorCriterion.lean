import MatrixCandidateSurjectivity
import PVConstantInjectivity

/-! Conditional canonical multiplication equivalence for the actual candidate.
B-flatness remains an explicit unproved input, as does the ambient constant-field
property. This constructs no bialgebra or coaction and asserts no PV existence. -/
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
variable {k B L n : Type*} [Field k] [CommRing B] [Field L]
  [Algebra k B] [Algebra k L] [Algebra B L] [IsScalarTower k B L]
  [Fintype n] [DecidableEq n]

/-- Actual candidate multiplication is bijective under the explicitly remaining
flatness and ambient-constants hypotheses. -/
theorem candidateConstantMultiplication_bijective
    (dB : Derivation k B B) (dL : Derivation k L L)
    (Y : Matrix n n L) (A : Matrix n n B) (hdet : Y.det ≠ 0)
    [Module.Flat B (matrixGeneratedAlgebra (B := B) Y)]
    (hb : ∀ b, dL (algebraMap B L b) = algebraMap B L (dB b))
    (hy : ∀ i j, dL (Y i j) = ∑ l, algebraMap B L (A i l) * Y l j)
    (hconstants : ∀ a, dL a = 0 → ∃ c : k, algebraMap k L c = a) :
    Function.Bijective (pvConstantMultiplication dB
      (candidateKDerivation dB dL Y A hb hy)
      (candidateKDerivation_base dB dL Y A hb hy)) := by
  constructor
  · exact pvConstantMultiplication_injective dB _ _ dL
      (matrixGeneratedAlgebra (B := B) Y).val Subtype.val_injective
      (fun _ => rfl) hconstants
  · exact candidateConstantMultiplication_surjective dB dL Y A hdet hb hy

def candidateConstantMultiplicationEquiv
    (dB : Derivation k B B) (dL : Derivation k L L)
    (Y : Matrix n n L) (A : Matrix n n B) (hdet : Y.det ≠ 0)
    [Module.Flat B (matrixGeneratedAlgebra (B := B) Y)]
    (hb : ∀ b, dL (algebraMap B L b) = algebraMap B L (dB b))
    (hy : ∀ i j, dL (Y i j) = ∑ l, algebraMap B L (A i l) * Y l j)
    (hconstants : ∀ a, dL a = 0 → ∃ c : k, algebraMap k L c = a) :=
  AlgEquiv.ofBijective (pvConstantMultiplication dB
      (candidateKDerivation dB dL Y A hb hy)
      (candidateKDerivation_base dB dL Y A hb hy))
    (candidateConstantMultiplication_bijective dB dL Y A hdet hb hy hconstants)

@[simp] theorem candidateConstantMultiplicationEquiv_apply
    (dB : Derivation k B B) (dL : Derivation k L L)
    (Y : Matrix n n L) (A : Matrix n n B) (hdet : Y.det ≠ 0)
    [Module.Flat B (matrixGeneratedAlgebra (B := B) Y)]
    (hb : ∀ b, dL (algebraMap B L b) = algebraMap B L (dB b))
    (hy : ∀ i j, dL (Y i j) = ∑ l, algebraMap B L (A i l) * Y l j)
    (hconstants : ∀ a, dL a = 0 → ∃ c : k, algebraMap k L c = a)
    (x : (matrixGeneratedAlgebra (B := B) Y) ⊗[k]
      pvConstantAlgebra dB (candidateKDerivation dB dL Y A hb hy)
        (candidateKDerivation_base dB dL Y A hb hy)) :
    candidateConstantMultiplicationEquiv dB dL Y A hdet hb hy hconstants x =
      pvConstantMultiplication dB (candidateKDerivation dB dL Y A hb hy)
        (candidateKDerivation_base dB dL Y A hb hy) x := rfl

#print axioms candidateConstantMultiplication_bijective
#print axioms candidateConstantMultiplicationEquiv
#print axioms candidateConstantMultiplicationEquiv_apply
end StrictEUnit
