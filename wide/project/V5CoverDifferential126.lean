import V5ComponentCoverFromOwnChart
import TensorDerivation

noncomputable section
open scoped TensorProduct
open TensorProduct
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule

variable {B k R H N : Type*}
  [CommRing B] [Field k] [CommRing R] [CommRing H] [CommRing N]
  [Algebra B R] [Algebra k B] [Algebra k R] [IsScalarTower k B R] [Algebra k H] [Algebra k N]

theorem v5_tensorDerivation_map_right_factor126 (d : Derivation k R R)
    (q : H →ₐ[k] N) (x : R ⊗[k] H) :
    tensorDerivation d (Algebra.TensorProduct.map (AlgHom.id B R) q x) =
      Algebra.TensorProduct.map (AlgHom.id B R) q (tensorDerivation d x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r h => simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, tensorDerivation_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem v5ComponentCover_differential126 (ρ : R →ₐ[B] R ⊗[k] H) (q : H →ₐ[k] N)
    (d : Derivation k R R) (hd : ∀ r, tensorDerivation d (ρ r) = ρ (d r))
    (x : v5ComponentCoverAlgebra ρ q) :
    d x.val ∈ v5ComponentCoverAlgebra ρ q := by
  have hx : Algebra.TensorProduct.map (AlgHom.id B R) q (ρ x.val) =
      x.val ⊗ₜ[k] (1 : N) := x.property
  change Algebra.TensorProduct.map (AlgHom.id B R) q (ρ (d x.val)) =
      d x.val ⊗ₜ[k] (1 : N)
  rw [← hd, ← v5_tensorDerivation_map_right_factor126, hx, tensorDerivation_tmul]

/-- Restriction of the own derivation to the restricted invariant subalgebra. -/
def v5ComponentCoverDerivation126 (ρ : R →ₐ[B] R ⊗[k] H) (q : H →ₐ[k] N)
    (d : Derivation k R R) (hd : ∀ r, tensorDerivation d (ρ r) = ρ (d r)) :
    Derivation k (v5ComponentCoverAlgebra ρ q) (v5ComponentCoverAlgebra ρ q) :=
  Derivation.mk'
    { toFun := fun x => ⟨d x.val, v5ComponentCover_differential126 ρ q d hd x⟩
      map_add' := fun x y => Subtype.ext (d.map_add x.val y.val)
      map_smul' := fun a x => Subtype.ext (d.map_smul a x.val) }
    (fun x y => Subtype.ext (d.leibniz x.val y.val))

theorem v5ComponentCoverDerivation126_base
    (ρ : R →ₐ[B] R ⊗[k] H) (q : H →ₐ[k] N)
    (d : Derivation k R R) (hd : ∀ r, tensorDerivation d (ρ r) = ρ (d r))
    (dB : Derivation k B B)
    (hB : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b)) (b : B) :
    v5ComponentCoverDerivation126 ρ q d hd (algebraMap B (v5ComponentCoverAlgebra ρ q) b) =
      algebraMap B (v5ComponentCoverAlgebra ρ q) (dB b) :=
  Subtype.ext (hB b)

end StrictEUnit
#print axioms StrictEUnit.v5_tensorDerivation_map_right_factor126
#print axioms StrictEUnit.v5ComponentCover_differential126
#print axioms StrictEUnit.v5ComponentCoverDerivation126
#print axioms StrictEUnit.v5ComponentCoverDerivation126_base
