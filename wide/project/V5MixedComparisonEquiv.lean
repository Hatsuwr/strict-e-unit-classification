import V5MixedComparisonInjectivity

open scoped TensorProduct
open TensorProduct
noncomputable section
namespace StrictEUnit
variable {k B R S E n : Type*} [Field k] [CommRing B] [CommRing R] [CommRing S] [Field E]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
  [Algebra k S] [Algebra B S] [IsScalarTower k B S]
  [Algebra k E] [Algebra B E] [IsScalarTower k B E] [Module.Flat B S]
  [Fintype n] [DecidableEq n]

/-- The mixed comparison with actual differential constants, given the explicit
flatness, differential embedding, and generating-solution hypotheses. -/
def v5MixedComparisonEquiv
    (dB : Derivation k B B) (dR : Derivation k R R) (dS : Derivation k S S)
    (hR : ∀ b, dR (algebraMap B R b) = algebraMap B R (dB b))
    (hS : ∀ b, dS (algebraMap B S b) = algebraMap B S (dB b))
    (dE : Derivation k E E) (f : R →ₐ[B] E) (hf : Function.Injective f)
    (hfD : ∀ r, dE (f r) = f (dR r))
    (hconstants : ∀ a, dE a = 0 → ∃ c : k, algebraMap k E c = a)
    (A : Matrix n n (R ⊗[B] S)) (Y : (Matrix n n R)ˣ) (v : n → S)
    (hY : matrixDerivative (mixedRelativeTensorDerivation dB dR dS hR hS)
        (v5MixedLeftMatrix (B := B) (S := S) Y : Matrix n n (R ⊗[B] S)) =
      A * (v5MixedLeftMatrix (B := B) (S := S) Y : Matrix n n (R ⊗[B] S)))
    (hv : ∀ i, mixedRelativeTensorDerivation dB dR dS hR hS ((1 : R) ⊗ₜ[B] v i) =
      (A.mulVec (fun j => (1 : R) ⊗ₜ[B] v j)) i)
    (hgen : Algebra.adjoin B (Set.range v) = ⊤) :
    R ⊗[k] derivationConstants (mixedRelativeTensorDerivation dB dR dS hR hS) ≃ₐ[R]
      R ⊗[B] S :=
  AlgEquiv.ofBijective (v5MixedConstantMultiplication _)
    ⟨v5_mixedConstantMultiplication_injective dB dR dS hR hS dE f hf hfD hconstants,
      v5_mixedConstantMultiplication_surjective _ A Y v hY hv hgen⟩

end StrictEUnit
#print axioms StrictEUnit.v5MixedComparisonEquiv
