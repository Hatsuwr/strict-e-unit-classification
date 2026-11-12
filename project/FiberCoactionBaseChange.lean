import AlgebraicFiber

/-! Identification of the fiber coaction with genuine tensor base change. -/
open scoped TensorProduct
open TensorProduct
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
variable {k B R H : Type*} [Field k] [CommRing B] [CommRing R] [CommRing H]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
  [Algebra B k] [IsScalarTower k B k] [Algebra k H]

def fiberCoactionBaseChange (ρ : R →ₐ[B] R ⊗[k] H) :
    (k ⊗[B] R) →ₐ[k] (k ⊗[B] R) ⊗[k] H :=
  (fiberMixedAssoc (k:=k) (B:=B) (A:=k)).symm.toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id k k) ρ)

@[simp] theorem fiberCoactionBaseChange_tmul (ρ : R →ₐ[B] R ⊗[k] H) (a:k) (r:R) :
    fiberCoactionBaseChange ρ (a ⊗ₜ[B] r) =
      (fiberMixedAssoc (k:=k) (B:=B) (A:=k)).symm (a ⊗ₜ[B] ρ r) := rfl

theorem fiberMultiplicationChart_forward
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) (z:(k ⊗[B] R) ⊗[k] H) :
    algebraTensorBaseChangeEquiv (k:=B) k R R (fiberMultiplicationChart (A:=k) e z) =
    Algebra.TensorProduct.map (AlgHom.id k k) (e.toAlgHom.restrictScalars B)
      (fiberMixedAssoc (k:=k) (B:=B) (A:=k) z) := by
  exact (algebraTensorBaseChangeEquiv (k:=B) k R R).apply_symm_apply _

/-- The canonical-chart construction equals the actual base-changed original coaction. -/
theorem algebraicFiberCoaction_eq_baseChange
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) :
    algebraicFiberCoaction e = fiberCoactionBaseChange (inverseMultiplicationCoaction e) := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a r =>
    apply (fiberMultiplicationChart (A:=k) e).injective
    change (fiberMultiplicationChart (A:=k) e)
      ((fiberMultiplicationChart (A:=k) e).symm ((1:k ⊗[B] R) ⊗ₜ[k] (a ⊗ₜ[B] r))) = _
    rw [AlgEquiv.apply_symm_apply]
    apply (algebraTensorBaseChangeEquiv (k:=B) k R R).injective
    rw [fiberMultiplicationChart_forward, fiberCoactionBaseChange_tmul,
      AlgEquiv.apply_symm_apply, Algebra.TensorProduct.map_tmul]
    change algebraTensorBaseChangeEquiv (k:=B) k R R
      (((1:k) ⊗ₜ[B] (1:R)) ⊗ₜ[k] (a ⊗ₜ[B] r)) =
        a ⊗ₜ[B] e (e.symm ((1:R) ⊗ₜ[B] r))
    rw [algebraTensorBaseChangeEquiv_tmul, one_mul, AlgEquiv.apply_symm_apply]
end StrictEUnit
#print axioms StrictEUnit.fiberCoactionBaseChange
#print axioms StrictEUnit.fiberCoactionBaseChange_tmul
#print axioms StrictEUnit.fiberMultiplicationChart_forward
#print axioms StrictEUnit.algebraicFiberCoaction_eq_baseChange
