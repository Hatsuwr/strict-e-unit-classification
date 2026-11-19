import TypedMorphismMaps
import PVConstantComultiplication
import CandidateCoaction

/-! Coassociativity of the actual candidate action, from the defining
multiplication chart and descended comultiplication. No action law is assumed. -/
open scoped TensorProduct
open TensorProduct
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
section Chart
variable {k B R H : Type*} [CommRing k] [CommRing B] [CommRing R] [CommRing H]
  [Algebra k B] [Algebra k R] [Algebra k H] [Algebra B R] [IsScalarTower k B R]

/-- The triple chart formula for a non-pure first pair. -/
theorem pvTripleChart_assoc_pair (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R)
    (z : R ⊗[k] H) (h : H) :
    pvTripleChart e (Algebra.TensorProduct.assoc k R H H (z ⊗ₜ[k] h)) =
      Algebra.TensorProduct.map (AlgHom.id B R) (e.toAlgHom.restrictScalars B)
        (mixedAlgebraAssoc (k:=k) (B:=B) (e z ⊗ₜ[k] h)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [TypedMaps.algEquiv_zero, TypedMaps.algHom_zero, tmul_zero, zero_tmul]
  | add x y hx hy => simp only [add_tmul, TypedMaps.algEquiv_add, TypedMaps.algHom_add, hx, hy]
  | tmul r g => exact pvTripleChart_tmul e r g h

/-- Applying the action on the first factor corresponds to prepending a unit
under the genuine triple chart. -/
theorem pvTripleChart_action_left (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R)
    (z : R ⊗[k] H) :
    pvTripleChart e (Algebra.TensorProduct.assoc k R H H
      (Algebra.TensorProduct.map ((inverseMultiplicationCoaction e).restrictScalars k)
        (AlgHom.id k H) z)) = (1:R) ⊗ₜ[B] e z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [TypedMaps.algEquiv_zero, TypedMaps.algHom_zero, tmul_zero, zero_tmul]
  | add x y hx hy => simp only [TypedMaps.algEquiv_add, TypedMaps.algHom_add, tmul_add, hx, hy]
  | tmul r h =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      AlgHom.restrictScalars_apply]
    rw [pvTripleChart_assoc_pair, inverseMultiplicationCoaction_apply,
      AlgEquiv.apply_symm_apply, mixedAlgebraAssoc_tmul]
    rfl
end Chart

section Constants
variable {k B R : Type*} [Field k] [CommRing B] [CommRing R] [Nontrivial R]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
variable (dB : Derivation k B B) (d : Derivation k R R)
  (hb : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
  (he : Function.Bijective (pvConstantMultiplication dB d hb))
  (hc : ∀ r, d r = 0 → ∃ c:k, algebraMap k R c = r)
local notation "H" => pvConstantAlgebra dB d hb
local notation "e" => AlgEquiv.ofBijective (pvConstantMultiplication dB d hb) he
local notation "Δ" => pvConstantComultiplication dB d hb he hc

/-- Applying descended comultiplication corresponds to inserting the middle unit. -/
theorem pvTripleChart_action_right (z : R ⊗[k] H) :
    pvTripleChart e (Algebra.TensorProduct.map (AlgHom.id R R) Δ z) =
      pvMiddleInsertion (k:=k) (e z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [TypedMaps.algEquiv_zero, TypedMaps.algHom_zero, tmul_zero, zero_tmul]
  | add x y hx hy => simp only [TypedMaps.algEquiv_add, TypedMaps.algHom_add, hx, hy]
  | tmul r h =>
    change pvTripleChart e (r ⊗ₜ[k] Δ h) =
      pvMiddleInsertion (k:=k) (pvConstantMultiplication dB d hb (r ⊗ₜ[k] h))
    have hr : pvTripleChart e (r ⊗ₜ[k] (1:H ⊗[k] H)) =
        r ⊗ₜ[B] (1:R ⊗[B] R) := (pvTripleChart e).commutes r
    have ht : r ⊗ₜ[k] Δ h =
        (r ⊗ₜ[k] (1:H ⊗[k] H)) * ((1:R) ⊗ₜ[k] Δ h) := by
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [ht, TypedMaps.algEquiv_mul, hr, pvConstantComultiplication_spec,
      pvConstantMultiplication_tmul, TypedMaps.algHom_mul, pvMiddleInsertion_tmul]
    rfl

/-- Actual coassociativity of rho=mu⁻¹(1 tensor r) and the actual descended Δ. -/
theorem inverseMultiplicationCoaction_coassoc (r : R) :
    Algebra.TensorProduct.assoc k R H H
      (Algebra.TensorProduct.map ((inverseMultiplicationCoaction e).restrictScalars k)
        (AlgHom.id k H) (inverseMultiplicationCoaction e r)) =
    Algebra.TensorProduct.map (AlgHom.id R R) Δ (inverseMultiplicationCoaction e r) := by
  apply (pvTripleChart e).injective
  rw [pvTripleChart_action_left, pvTripleChart_action_right,
    inverseMultiplicationCoaction_apply, AlgEquiv.apply_symm_apply]
  rfl
end Constants
end StrictEUnit
#print axioms StrictEUnit.pvTripleChart_assoc_pair
#print axioms StrictEUnit.pvTripleChart_action_left
#print axioms StrictEUnit.pvTripleChart_action_right
#print axioms StrictEUnit.inverseMultiplicationCoaction_coassoc
