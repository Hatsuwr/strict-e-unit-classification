import TypedMorphismMaps
import FiberCoactionBaseChange

/-! Coassociativity survives the genuine base change to an algebraic fiber.
No flatness, reducedness, or domain premise on the fiber is used. -/
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
local notation "S" => k ⊗[B] R

@[simp] theorem fiberMixedAssoc_symm_tmul (a:k) (r:R) (h:H) :
    (fiberMixedAssoc (k:=k) (B:=B) (A:=k)).symm (a ⊗ₜ[B] (r ⊗ₜ[k] h)) =
      (a ⊗ₜ[B] r) ⊗ₜ[k] h := rfl

/-- The two genuine associators agree when a final constant factor is appended. -/
theorem fiberTriple_assoc_pair (a:k) (z:R ⊗[k] H) (h:H) :
    fiberMixedAssoc (k:=k) (B:=B) (A:=k)
      (Algebra.TensorProduct.assoc k S H H
        ((fiberMixedAssoc (k:=k) (B:=B) (A:=k)).symm (a ⊗ₜ[B] z) ⊗ₜ[k] h)) =
      a ⊗ₜ[B] (Algebra.TensorProduct.assoc k R H H (z ⊗ₜ[k] h)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [TypedMaps.algEquiv_zero, TypedMaps.algHom_zero, tmul_zero, zero_tmul]
  | add x y hx hy => simp only [tmul_add, TypedMaps.algEquiv_add, TypedMaps.algHom_add, add_tmul, hx, hy]
  | tmul r g => rfl

/-- Naturality of the first coaction leg under fiber base change. -/
theorem fiberCoaction_left_diagram (ρ : R →ₐ[B] R ⊗[k] H)
    (a:k) (z:R ⊗[k] H) :
    fiberMixedAssoc (k:=k) (B:=B) (A:=k)
      (Algebra.TensorProduct.assoc k S H H
        (Algebra.TensorProduct.map (fiberCoactionBaseChange ρ) (AlgHom.id k H)
          ((fiberMixedAssoc (k:=k) (B:=B) (A:=k)).symm (a ⊗ₜ[B] z)))) =
      a ⊗ₜ[B] (Algebra.TensorProduct.assoc k R H H
        (Algebra.TensorProduct.map (ρ.restrictScalars k) (AlgHom.id k H) z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [TypedMaps.algEquiv_zero, TypedMaps.algHom_zero, tmul_zero, zero_tmul]
  | add x y hx hy => simp only [tmul_add, TypedMaps.algEquiv_add, TypedMaps.algHom_add, hx, hy]
  | tmul r h =>
    simp only [fiberMixedAssoc_symm_tmul, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, AlgHom.restrictScalars_apply, fiberCoactionBaseChange_tmul]
    exact fiberTriple_assoc_pair a (ρ r) h

/-- Naturality of the second, comultiplication leg under fiber base change. -/
theorem fiberCoaction_right_diagram (Δ : H →ₐ[k] H ⊗[k] H)
    (a:k) (z:R ⊗[k] H) :
    fiberMixedAssoc (k:=k) (B:=B) (A:=k)
      (Algebra.TensorProduct.map (AlgHom.id k S) Δ
        ((fiberMixedAssoc (k:=k) (B:=B) (A:=k)).symm (a ⊗ₜ[B] z))) =
      a ⊗ₜ[B] (Algebra.TensorProduct.map (AlgHom.id k R) Δ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [TypedMaps.algEquiv_zero, TypedMaps.algHom_zero, tmul_zero, zero_tmul]
  | add x y hx hy => simp only [tmul_add, TypedMaps.algEquiv_add, TypedMaps.algHom_add, hx, hy]
  | tmul r h => rfl

/-- The base-changed action satisfies the original comultiplication law. -/
theorem fiberCoactionBaseChange_coassoc (ρ : R →ₐ[B] R ⊗[k] H)
    (Δ : H →ₐ[k] H ⊗[k] H)
    (hρ : ∀ r:R, Algebra.TensorProduct.assoc k R H H
      (Algebra.TensorProduct.map (ρ.restrictScalars k) (AlgHom.id k H) (ρ r)) =
      Algebra.TensorProduct.map (AlgHom.id k R) Δ (ρ r)) (x:S) :
    Algebra.TensorProduct.assoc k S H H
      (Algebra.TensorProduct.map (fiberCoactionBaseChange ρ) (AlgHom.id k H)
        (fiberCoactionBaseChange ρ x)) =
      Algebra.TensorProduct.map (AlgHom.id k S) Δ (fiberCoactionBaseChange ρ x) := by
  apply (fiberMixedAssoc (k:=k) (B:=B) (A:=k) (R:=R) (H:=H ⊗[k] H)).injective
  induction x using TensorProduct.induction_on with
  | zero => simp only [TypedMaps.algEquiv_zero, TypedMaps.algHom_zero, tmul_zero, zero_tmul]
  | add x y hx hy => simp only [TypedMaps.algEquiv_add, TypedMaps.algHom_add, hx, hy]
  | tmul a r =>
    rw [fiberCoactionBaseChange_tmul, fiberCoaction_left_diagram, fiberCoaction_right_diagram, hρ]

/-- The canonical-chart fiber action has this law, not merely a replacement map. -/
theorem algebraicFiberCoaction_coassoc
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) (Δ : H →ₐ[k] H ⊗[k] H)
    (hρ : ∀ r:R, Algebra.TensorProduct.assoc k R H H
      (Algebra.TensorProduct.map ((inverseMultiplicationCoaction e).restrictScalars k)
        (AlgHom.id k H) (inverseMultiplicationCoaction e r)) =
      Algebra.TensorProduct.map (AlgHom.id k R) Δ (inverseMultiplicationCoaction e r)) (x:S) :
    Algebra.TensorProduct.assoc k S H H
      (Algebra.TensorProduct.map (algebraicFiberCoaction e) (AlgHom.id k H)
        (algebraicFiberCoaction e x)) =
      Algebra.TensorProduct.map (AlgHom.id k S) Δ (algebraicFiberCoaction e x) := by
  rw [algebraicFiberCoaction_eq_baseChange]
  exact fiberCoactionBaseChange_coassoc (inverseMultiplicationCoaction e) Δ hρ x
end StrictEUnit
#print axioms StrictEUnit.fiberMixedAssoc_symm_tmul
#print axioms StrictEUnit.fiberTriple_assoc_pair
#print axioms StrictEUnit.fiberCoaction_left_diagram
#print axioms StrictEUnit.fiberCoaction_right_diagram
#print axioms StrictEUnit.fiberCoactionBaseChange_coassoc
#print axioms StrictEUnit.algebraicFiberCoaction_coassoc
