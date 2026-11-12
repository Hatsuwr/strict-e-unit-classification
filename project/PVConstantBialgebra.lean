import TypedMorphismMaps
import PVCoassociativity
import Mathlib.RingTheory.Bialgebra.Basic

/-! A genuine bialgebra on diagonal constants, conditional on the proved
multiplication equivalence and exact scalar constants. No antipode yet. -/
open scoped TensorProduct
open TensorProduct
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k B R : Type*} [Field k] [CommRing B] [CommRing R] [Nontrivial R]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
variable (dB : Derivation k B B) (d : Derivation k R R)
  (hb : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
  (he : Function.Bijective (pvConstantMultiplication dB d hb))
  (hc : ∀ r, d r = 0 → ∃ c:k, algebraMap k R c = r)
local notation "H" => pvConstantAlgebra dB d hb
local notation "Δ" => pvConstantComultiplication dB d hb he hc
local notation "ε" => candidateCounit dB d hb hc

theorem pvLeftCounitContraction_eq (z:H ⊗[k] H) :
    Algebra.TensorProduct.lid k H
      (Algebra.TensorProduct.map ε (AlgHom.id k H) z) =
      pvLeftCounitContraction dB d hb hc z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [TypedMaps.algEquiv_zero, TypedMaps.algHom_zero, tmul_zero, zero_tmul, ZeroMemClass.coe_zero]
  | add x y hx hy => simp only [TypedMaps.algEquiv_add, TypedMaps.algHom_add, hx, hy]
  | tmul h g =>
    change (ε h) • g = algebraMap k H (ε h) * g
    exact Algebra.smul_def _ _

theorem pvRightCounitContraction_eq (z:H ⊗[k] H) :
    Algebra.TensorProduct.rid k k H
      (Algebra.TensorProduct.map (AlgHom.id k H) ε z) =
      pvRightCounitContraction dB d hb hc z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [TypedMaps.algEquiv_zero, TypedMaps.algHom_zero, tmul_zero, zero_tmul, ZeroMemClass.coe_zero]
  | add x y hx hy => simp only [TypedMaps.algEquiv_add, TypedMaps.algHom_add, hx, hy]
  | tmul h g =>
    change (ε g) • h = h * algebraMap k H (ε g)
    rw [Algebra.smul_def, mul_comm]

theorem pvConstantComultiplication_counit_left :
    (Algebra.TensorProduct.map ε (AlgHom.id k H)).comp Δ =
      (Algebra.TensorProduct.lid k H).symm.toAlgHom := by
  apply AlgHom.ext
  intro h
  apply (Algebra.TensorProduct.lid k H).injective
  change Algebra.TensorProduct.lid k H
    (Algebra.TensorProduct.map ε (AlgHom.id k H) (Δ h)) = _
  rw [pvLeftCounitContraction_eq, pvConstantComultiplication_left_counit]
  exact ((Algebra.TensorProduct.lid k H).apply_symm_apply h).symm

theorem pvConstantComultiplication_counit_right :
    (Algebra.TensorProduct.map (AlgHom.id k H) ε).comp Δ =
      (Algebra.TensorProduct.rid k k H).symm.toAlgHom := by
  apply AlgHom.ext
  intro h
  apply (Algebra.TensorProduct.rid k k H).injective
  change Algebra.TensorProduct.rid k k H
    (Algebra.TensorProduct.map (AlgHom.id k H) ε (Δ h)) = _
  rw [pvRightCounitContraction_eq, pvConstantComultiplication_right_counit]
  exact ((Algebra.TensorProduct.rid k k H).apply_symm_apply h).symm

/-- All bialgebra laws are supplied by proofs, not assumptions or structure fields. -/
def pvConstantBialgebra : Bialgebra k H :=
  Bialgebra.ofAlgHom Δ ε
    (AlgHom.ext (pvConstantComultiplication_coassoc dB d hb he hc))
    (pvConstantComultiplication_counit_left dB d hb he hc)
    (pvConstantComultiplication_counit_right dB d hb he hc)

end StrictEUnit
#print axioms StrictEUnit.pvLeftCounitContraction_eq
#print axioms StrictEUnit.pvRightCounitContraction_eq
#print axioms StrictEUnit.pvConstantComultiplication_counit_left
#print axioms StrictEUnit.pvConstantComultiplication_counit_right
#print axioms StrictEUnit.pvConstantBialgebra
