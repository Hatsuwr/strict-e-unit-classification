import CanonicalInvariants
import ScalarExtendedCanonicalUnitLift
import DifferentialCharacter

/-! The character-lifting and logarithmic-derivative arguments assembled
from canonical torsor hypotheses. Differential compatibility remains explicit;
no actual Picard–Vessiot ring is asserted to have been constructed. -/
open TensorProduct
open scoped TensorProduct
noncomputable section
set_option maxHeartbeats 200000
namespace StrictEUnit
variable {k B R H : Type*} [CommRing k] [CommRing B] [Algebra k B]
  [CommRing R] [Algebra B R] [Algebra k R] [IsScalarTower k B R]
  [CommRing H]

section General
variable [Algebra k H]

/-- Remove the actual scalar extension in the coaction target using the
standard mixed-base tensor equivalence. -/
def constantFieldCoaction (ρ : R →ₐ[B] R ⊗[B] (B ⊗[k] H)) :
    R →ₐ[B] R ⊗[k] H :=
  (Algebra.TensorProduct.cancelBaseChange k B B R H).toAlgHom.comp ρ

@[simp] theorem constantFieldCoaction_apply
    (ρ : R →ₐ[B] R ⊗[B] (B ⊗[k] H)) (r : R) :
    constantFieldCoaction ρ r =
      Algebra.TensorProduct.cancelBaseChange k B B R H (ρ r) := rfl

end General
variable [Bialgebra k H]

/-- Invariant base membership is derived from the canonical torsor criterion,
not supplied as a global or local invariant-image premise. -/
theorem scalar_extended_canonical_invariants
    [Module.FaithfullyFlat B R]
    (ρ : R →ₐ[B] R ⊗[B] (B ⊗[k] H))
    (hcan : Function.Bijective (torsorCanonical ρ))
    (hcoassoc : ∀ s : R,
      Algebra.TensorProduct.assoc B R (B ⊗[k] H) (B ⊗[k] H)
        (Algebra.TensorProduct.map ρ (AlgHom.id B (B ⊗[k] H)) (ρ s)) =
      weightBaseChangeAlgHom R (baseChangeComul (k := k) (H := H) B) (ρ s))
    (r : R) (hr : constantFieldCoaction ρ r = r ⊗ₜ[k] (1 : H)) :
    ∃ b : B, algebraMap B R b = r := by
  letI := baseChangeBialgebra (k := k) (H := H) B
  apply canonical_torsor_invariants_are_scalars ρ hcan hcoassoc r
  apply (Algebra.TensorProduct.cancelBaseChange k B B R H).injective
  simpa only [Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.one_def, Algebra.TensorProduct.cancelBaseChange_tmul,
    one_smul] using hr

/-- A constant-field character on a differential canonical torsor lifts to
an actual regular unit satisfying a first-order equation with coefficient in B.
The existence of that coefficient is a conclusion, not a premise. -/
theorem exists_character_unit_first_order_equation
    [IsDomain B] [UniqueFactorizationMonoid B] [IsDomain R]
    [Module.FaithfullyFlat B R]
    (ρ : R →ₐ[B] R ⊗[B] (B ⊗[k] H))
    (hcan : Function.Bijective (torsorCanonical ρ))
    (hcoassoc : ∀ s : R,
      Algebra.TensorProduct.assoc B R (B ⊗[k] H) (B ⊗[k] H)
        (Algebra.TensorProduct.map ρ (AlgHom.id B (B ⊗[k] H)) (ρ s)) =
      weightBaseChangeAlgHom R (baseChangeComul (k := k) (H := H) B) (ρ s))
    (δ : Derivation k R R)
    (hδ : ∀ r, constantFieldCoaction ρ (δ r) =
      tensorDerivation δ (constantFieldCoaction ρ r))
    (χ : Hˣ)
    (hχ : Coalgebra.comul (R := k) (χ : H) = (χ : H) ⊗ₜ[k] (χ : H)) :
    ∃ v : Rˣ, ∃ b : B,
      ρ (v : R) = (v : R) ⊗ₜ[B] ((1 : B) ⊗ₜ[k] (χ : H)) ∧
      δ (v : R) = algebraMap B R b * (v : R) := by
  obtain ⟨v, w, hv, hw, hvw, hu⟩ :=
    exists_character_unit_of_scalar_extended_canonical_torsor ρ hcan hcoassoc χ hχ
  obtain ⟨u, rfl⟩ := hu
  have hm : constantFieldCoaction ρ (u : R) = (u : R) ⊗ₜ[k] (χ : H) := by
    rw [constantFieldCoaction_apply, hv,
      Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]
  obtain ⟨b, hb⟩ := logarithmic_derivative_in_base δ (constantFieldCoaction ρ) hδ
    (fun r hr => scalar_extended_canonical_invariants ρ hcan hcoassoc r hr) χ u hm
  refine ⟨u, b, hv, ?_⟩
  have he := congrArg (fun x : R => x * (u : R)) hb
  calc
    δ (u : R) = ((↑u⁻¹ : R) * δ (u : R)) * (u : R) := by
      rw [mul_right_comm, Units.inv_mul, one_mul]
    _ = algebraMap B R b * (u : R) := he.symm
end StrictEUnit
#print axioms StrictEUnit.constantFieldCoaction
#print axioms StrictEUnit.constantFieldCoaction_apply
#print axioms StrictEUnit.scalar_extended_canonical_invariants
#print axioms StrictEUnit.exists_character_unit_first_order_equation
