import V5ComponentCoverFromOwnChart
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
variable {k B R H : Type*} [Field k] [CommRing B] [CommRing R] [CommRing H]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R] [Algebra k H]
/-- Quotient-specialized trivial square, reducing concrete instance inference. -/
def v5QuotientTrivialSquare128
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) (I : Ideal H) :=
  v5OwnTrivialTorsorSquareR (N := H ⧸ I) e.symm
/-- Quotient-specialized restricted square with the canonical coaction. -/
def v5QuotientRestrictedSquare128
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) (I : Ideal H)
    (Δ : H →ₐ[k] H ⊗[k] H)
    (hρ : ∀ r, Algebra.TensorProduct.assoc k R H H
      (Algebra.TensorProduct.map ((inverseMultiplicationCoaction e).restrictScalars k)
        (AlgHom.id k H) (inverseMultiplicationCoaction e r)) =
      Algebra.TensorProduct.map (AlgHom.id k R) Δ (inverseMultiplicationCoaction e r)) :=
  v5OwnRestrictedTorsorSquareR e.symm (inverseMultiplicationCoaction e) Δ
    (Ideal.Quotient.mkₐ k I) (v5_ownChart_tmul_smul e) hρ
end StrictEUnit
#print axioms StrictEUnit.v5QuotientTrivialSquare128
#print axioms StrictEUnit.v5QuotientRestrictedSquare128
