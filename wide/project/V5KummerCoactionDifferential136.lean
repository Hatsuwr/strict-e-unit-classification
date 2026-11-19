import V5KummerCoaction135
import MixedRelativeTensorDerivation
import TensorDerivation
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
set_option maxHeartbeats 600000
set_option maxRecDepth 1600
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
local instance algebraSMulCommDiff136 (A B C : Type*) [CommRing A] [CommRing B]
    [CommRing C] [Algebra A C] [Algebra B C] : SMulCommClass A B C :=
  ⟨fun a b c => by simp only [Algebra.smul_def]; exact mul_left_comm _ _ _⟩
variable {k T L R N : Type*}
  [CommRing k] [CommRing T] [CommRing L] [CommRing R] [CommRing N]
  [Algebra k T] [Algebra k L] [Algebra k R] [Algebra k N]
  [Algebra T L] [Algebra T R] [IsScalarTower k T L] [IsScalarTower k T R]
/-- The Kummer base-change coaction commutes with the balanced derivation.
The quotient factor is constant and needs no bialgebra structure. -/
theorem v5KummerCoaction135_differential136
    (dT : Derivation k T T) (dL : Derivation k L L) (dR : Derivation k R R)
    (hL : ∀ t, dL (algebraMap T L t) = algebraMap T L (dT t))
    (hR : ∀ t, dR (algebraMap T R t) = algebraMap T R (dT t))
    (ρ : R →ₐ[T] R ⊗[k] N)
    (hρ : ∀ r, tensorDerivation dR (ρ r) = ρ (dR r))
    (x : L ⊗[T] R) :
    tensorDerivation (mixedRelativeTensorDerivation dT dL dR hL hR)
      (v5KummerCoaction135 ρ x) =
    v5KummerCoaction135 ρ (mixedRelativeTensorDerivation dT dL dR hL hR x) := by
  let d := mixedRelativeTensorDerivation dT dL dR hL hR
  let E := (v5KummerTensorAssoc135 (k := k) (T := T) (L := L) (R := R) (N := N)).symm
  have hshuffle (l : L) (z : R ⊗[k] N) :
      tensorDerivation d (E (l ⊗ₜ[T] z)) =
        E (dL l ⊗ₜ[T] z + l ⊗ₜ[T] tensorDerivation dR z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw =>
      simp only [TensorProduct.tmul_add, map_add] at hz hw ⊢
      rw [hz, hw]
      abel
    | tmul r n =>
      change tensorDerivation d ((l ⊗ₜ[T] r) ⊗ₜ[k] n) = _
      rw [tensorDerivation_tmul]
      change (dL l ⊗ₜ[T] r + l ⊗ₜ[T] dR r) ⊗ₜ[k] n = _
      rw [TensorProduct.add_tmul]
      rfl
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul l r =>
    rw [v5KummerCoaction135_tmul]
    change tensorDerivation d (E (l ⊗ₜ[T] ρ r)) = _
    rw [hshuffle, hρ]
    change E (dL l ⊗ₜ[T] ρ r + l ⊗ₜ[T] ρ (dR r)) =
      v5KummerCoaction135 ρ (dL l ⊗ₜ[T] r + l ⊗ₜ[T] dR r)
    rw [map_add, map_add, v5KummerCoaction135_tmul, v5KummerCoaction135_tmul]
/-- Balanced derivation and literal pure-tensor/differential coaction data
packaged together before specializing large actual rings. -/
theorem v5KummerDifferentialData136
    (dT : Derivation k T T) (dL : Derivation k L L) (dR : Derivation k R R)
    (hL : ∀ t, dL (algebraMap T L t) = algebraMap T L (dT t))
    (hR : ∀ t, dR (algebraMap T R t) = algebraMap T R (dT t))
    (ρ : R →ₐ[T] R ⊗[k] N)
    (hρ : ∀ r, tensorDerivation dR (ρ r) = ρ (dR r)) :
    ∃ d : Derivation k (L ⊗[T] R) (L ⊗[T] R),
      (∀ l r, d (l ⊗ₜ[T] r) = dL l ⊗ₜ[T] r + l ⊗ₜ[T] dR r) ∧
      ∀ x, tensorDerivation d (v5KummerCoaction135 ρ x) =
        v5KummerCoaction135 ρ (d x) :=
  ⟨mixedRelativeTensorDerivation dT dL dR hL hR,
    fun _ _ => rfl, v5KummerCoaction135_differential136 dT dL dR hL hR ρ hρ⟩
end StrictEUnit
#print axioms StrictEUnit.v5KummerCoaction135_differential136
#print axioms StrictEUnit.v5KummerDifferentialData136
