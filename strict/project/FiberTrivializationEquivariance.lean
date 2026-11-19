import FiberCoactionCoassociativity

/-! Equivariance of the derived algebraic fiber trivialization.
The chosen algebraic point is proved to exist. It is not identified with
numerical evaluation, nor is the fiber assumed to be a domain. -/
open scoped TensorProduct
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
variable {k B R H : Type*} [Field k] [IsAlgClosed k]
  [CommRing B] [CommRing R] [CommRing H] [Bialgebra k H]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
  [Algebra B k] [IsScalarTower k B k]
  [Algebra.FiniteType B R] [Module.FaithfullyFlat B R]

/-- The genuine algebraic trivialization is equivariant from the proved
base-changed action law, with no point or chart-equivalence premise. -/
theorem algebraicFiberTrivialization_coaction
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R)
    (hρ : ∀ r:R, Algebra.TensorProduct.assoc k R H H
      (Algebra.TensorProduct.map ((inverseMultiplicationCoaction e).restrictScalars k)
        (AlgHom.id k H) (inverseMultiplicationCoaction e r)) =
      weightBaseChangeAlgHom R (Bialgebra.comulAlgHom k H) (inverseMultiplicationCoaction e r))
    (x : k ⊗[B] R) :
    numericalTensorChart (algebraicFiberTrivialization e) (algebraicFiberCoaction e x) =
      Coalgebra.comul (R:=k) (algebraicFiberTrivialization e x) := by
  exact pointedTorsorEquiv_coaction (algebraicFiberCoaction e)
    (Classical.choice (algebraicFiber_has_point (k:=k) (B:=B) (R:=R)))
    (algebraicFiberCanonical_bijective e)
    (algebraicFiberCoaction_coassoc e (Bialgebra.comulAlgHom k H) hρ) x
end StrictEUnit
#print axioms StrictEUnit.algebraicFiberTrivialization_coaction
