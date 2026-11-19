import V5MixedRelativeCounit
import CandidateActionCoassociativity

open scoped TensorProduct
open TensorProduct
noncomputable section
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 40000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k B R S H : Type*} [CommRing k] [CommRing B] [CommRing R]
  [CommRing S] [CommRing H]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
  [Algebra k S] [Algebra B S] [IsScalarTower k B S] [Algebra k H]
local notation "M" => R ⊗[B] S

/-- The heterogeneous shuffle respects appending a final constant factor. -/
theorem v5MixedCoactionShuffle_assoc (s : S) (z : R ⊗[k] H) (h : H) :
    Algebra.TensorProduct.assoc k M H H
      (v5MixedCoactionShuffle (s ⊗ₜ[B] z) ⊗ₜ[k] h) =
    v5MixedCoactionShuffle
      (s ⊗ₜ[B] Algebra.TensorProduct.assoc k R H H (z ⊗ₜ[k] h)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [tmul_zero, zero_tmul, map_zero]
  | add x y hx hy => simp only [tmul_add, add_tmul, map_add, hx, hy]
  | tmul r g =>
    simp only [v5MixedCoactionShuffle_tmul, Algebra.TensorProduct.assoc_tmul]

/-- Naturality of the first action leg under mixed base change. -/
theorem v5MixedRelativeCoaction_left_diagram (ρ : R →ₐ[B] R ⊗[k] H)
    (s : S) (z : R ⊗[k] H) :
    Algebra.TensorProduct.assoc k M H H
      (Algebra.TensorProduct.map (v5MixedRelativeCoaction ρ) (AlgHom.id k H)
        (v5MixedCoactionShuffle (s ⊗ₜ[B] z))) =
    v5MixedCoactionShuffle
      (s ⊗ₜ[B] Algebra.TensorProduct.assoc k R H H
        (Algebra.TensorProduct.map (ρ.restrictScalars k) (AlgHom.id k H) z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [tmul_zero, map_zero]
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
  | tmul r h =>
    simp only [v5MixedCoactionShuffle_tmul, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, AlgHom.restrictScalars_apply, v5MixedRelativeCoaction_tmul]
    exact v5MixedCoactionShuffle_assoc s (ρ r) h

/-- Naturality of the comultiplication leg under mixed base change. -/
theorem v5MixedRelativeCoaction_right_diagram (Δ : H →ₐ[k] H ⊗[k] H)
    (s : S) (z : R ⊗[k] H) :
    Algebra.TensorProduct.map (AlgHom.id k M) Δ
      (v5MixedCoactionShuffle (s ⊗ₜ[B] z)) =
    v5MixedCoactionShuffle
      (s ⊗ₜ[B] Algebra.TensorProduct.map (AlgHom.id k R) Δ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [tmul_zero, map_zero]
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
  | tmul r h =>
    simp only [v5MixedCoactionShuffle_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

/-- The right coaction law on R survives genuine mixed relative base change.
No coaction, domain, reducedness, or torsor premise on S is used. -/
theorem v5MixedRelativeCoaction_coassoc (ρ : R →ₐ[B] R ⊗[k] H)
    (Δ : H →ₐ[k] H ⊗[k] H)
    (hρ : ∀ r, Algebra.TensorProduct.assoc k R H H
      (Algebra.TensorProduct.map (ρ.restrictScalars k) (AlgHom.id k H) (ρ r)) =
      Algebra.TensorProduct.map (AlgHom.id k R) Δ (ρ r)) (x : M) :
    Algebra.TensorProduct.assoc k M H H
      (Algebra.TensorProduct.map (v5MixedRelativeCoaction ρ) (AlgHom.id k H)
        (v5MixedRelativeCoaction ρ x)) =
      Algebra.TensorProduct.map (AlgHom.id k M) Δ (v5MixedRelativeCoaction ρ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r s =>
    rw [v5MixedRelativeCoaction_tmul, v5MixedRelativeCoaction_left_diagram,
      v5MixedRelativeCoaction_right_diagram, hρ]

end StrictEUnit
#print axioms StrictEUnit.v5MixedCoactionShuffle_assoc
#print axioms StrictEUnit.v5MixedRelativeCoaction_left_diagram
#print axioms StrictEUnit.v5MixedRelativeCoaction_right_diagram
#print axioms StrictEUnit.v5MixedRelativeCoaction_coassoc
