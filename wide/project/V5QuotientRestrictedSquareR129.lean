import V5QuotientSquares128
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
variable {k B R H : Type*} [Field k] [CommRing B] [CommRing R] [CommRing H]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R] [Algebra k H]

private theorem map_id_change_scalar129 {N : Type*} [CommRing N] [Algebra k N]
    (φ : H →ₐ[k] N) (x : R ⊗[k] H) :
    Algebra.TensorProduct.map (AlgHom.id R R) φ x =
      Algebra.TensorProduct.map (AlgHom.id k R) φ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul r h => simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The restricted square accepts the literal R-linear RHS of actual
coassociativity; scalar rebundling occurs only at generic types. -/
def v5QuotientRestrictedSquareR129
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) (I : Ideal H)
    (Δ : H →ₐ[k] H ⊗[k] H)
    (hρ : ∀ r, Algebra.TensorProduct.assoc k R H H
      (Algebra.TensorProduct.map ((inverseMultiplicationCoaction e).restrictScalars k)
        (AlgHom.id k H) (inverseMultiplicationCoaction e r)) =
      Algebra.TensorProduct.map (AlgHom.id R R) Δ (inverseMultiplicationCoaction e r)) :=
  v5QuotientRestrictedSquare128 e I Δ
    (fun r => (hρ r).trans (map_id_change_scalar129 _ _))
/-- Variant keeps the coaction as an explicit parameter, avoiding unfolding
an actual canonical-chart construction while checking its coassociativity. -/
def v5RestrictedSquareExplicitR129
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) (I : Ideal H)
    (ρ : R →ₐ[B] R ⊗[k] H) (Δ : H →ₐ[k] H ⊗[k] H)
    (he : ∀ r s, e.symm (r ⊗ₜ[B] s) = r • ρ s)
    (hρ : ∀ r, Algebra.TensorProduct.assoc k R H H
      (Algebra.TensorProduct.map (ρ.restrictScalars k) (AlgHom.id k H) (ρ r)) =
      Algebra.TensorProduct.map (AlgHom.id R R) Δ (ρ r)) :=
  v5OwnRestrictedTorsorSquareR e.symm ρ Δ (Ideal.Quotient.mkₐ k I) he
    (fun r => (hρ r).trans (map_id_change_scalar129 _ _))
end StrictEUnit
#print axioms StrictEUnit.v5QuotientRestrictedSquareR129
#print axioms StrictEUnit.v5RestrictedSquareExplicitR129
