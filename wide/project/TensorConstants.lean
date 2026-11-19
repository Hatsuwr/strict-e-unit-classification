import Mathlib.LinearAlgebra.Basis.VectorSpace
import PVConstantAlgebra
import Mathlib.RingTheory.Flat.Basic

/-! Exact constants of δ tensor identity, proved by tensor preservation of
the actual kernel sequence. No Hopf structure is constructed here. -/
open scoped TensorProduct
open TensorProduct
noncomputable section
namespace StrictEUnit
variable {k R H : Type*} [Field k] [CommRing R] [CommRing H]
  [Algebra k R] [Algebra k H]

/-- The scalar kernel sequence really is exact under the stated
constant-field hypothesis. -/
theorem derivation_scalar_sequence_exact (δ : Derivation k R R)
    (hconstants : ∀ r : R, δ r = 0 → ∃ c : k, algebraMap k R c = r) :
    Function.Exact (Algebra.linearMap k R) δ.toLinearMap := by
  intro r
  constructor
  · exact hconstants r
  · rintro ⟨c, rfl⟩
    exact δ.map_algebraMap c

/-- Tensoring the scalar inclusion is inclusion of the right factor
after the actual unitor. -/
theorem scalar_inclusion_rTensor (z : k ⊗[k] H) :
    (Algebra.linearMap k R).rTensor H z =
      (1 : R) ⊗ₜ[k] (TensorProduct.lid k H z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c h =>
    simp only [LinearMap.rTensor_tmul, Algebra.linearMap_apply,
      TensorProduct.lid_tmul]
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  | add x y hx hy => simp only [map_add, tmul_add, hx, hy]

/-- All constants after tensor extension come from the right factor. -/
theorem tensorDerivation_constants (δ : Derivation k R R)
    (hconstants : ∀ r : R, δ r = 0 → ∃ c : k, algebraMap k R c = r)
    (z : R ⊗[k] H) :
    tensorDerivation δ z = 0 ↔ ∃ h : H, (1 : R) ⊗ₜ[k] h = z := by
  constructor
  · intro hz
    have hex := Module.Flat.rTensor_exact H (derivation_scalar_sequence_exact δ hconstants)
    obtain ⟨y, hy⟩ := (hex z).mp hz
    exact ⟨TensorProduct.lid k H y, (scalar_inclusion_rTensor y).symm.trans hy⟩
  · rintro ⟨h, rfl⟩
    simp only [tensorDerivation_tmul, Derivation.map_one_eq_zero, zero_tmul]

/-- Actual right-factor inclusion into the constants subalgebra. -/
def tensorConstantsInclusion (δ : Derivation k R R) :
    H →ₐ[k] derivationConstants (tensorDerivation (H := H) δ) :=
  (Algebra.TensorProduct.includeRight : H →ₐ[k] R ⊗[k] H).codRestrict
    (derivationConstants (tensorDerivation δ)) (by
      intro h
      change tensorDerivation δ ((1 : R) ⊗ₜ[k] h) = 0
      simp only [tensorDerivation_tmul, Derivation.map_one_eq_zero, zero_tmul])

/-- With a nonzero left algebra, the constant representation is unique. -/
theorem tensorDerivation_constants_unique [Nontrivial R] (δ : Derivation k R R)
    (hconstants : ∀ r : R, δ r = 0 → ∃ c : k, algebraMap k R c = r)
    (z : R ⊗[k] H) (hz : tensorDerivation δ z = 0) :
    ∃! h : H, (1 : R) ⊗ₜ[k] h = z := by
  obtain ⟨h, hh⟩ := (tensorDerivation_constants δ hconstants z).mp hz
  refine ⟨h, hh, ?_⟩
  intro h' hh'
  apply Algebra.TensorProduct.includeRight_injective (RingHom.injective (algebraMap k R))
  exact hh'.trans hh.symm

/-- The constants are genuinely algebra-isomorphic to H, not merely
identified by a supplied surjectivity hypothesis. -/
def tensorConstantsEquiv [Nontrivial R] (δ : Derivation k R R)
    (hconstants : ∀ r : R, δ r = 0 → ∃ c : k, algebraMap k R c = r) :
    H ≃ₐ[k] derivationConstants (tensorDerivation (H := H) δ) :=
  AlgEquiv.ofBijective (tensorConstantsInclusion δ) ⟨by
    intro x y hxy
    apply Algebra.TensorProduct.includeRight_injective (RingHom.injective (algebraMap k R))
    exact congrArg Subtype.val hxy, by
    intro z
    obtain ⟨h, hh⟩ := (tensorDerivation_constants δ hconstants (z : R ⊗[k] H)).mp z.property
    exact ⟨h, Subtype.ext hh⟩⟩

@[simp] theorem tensorConstantsEquiv_coe [Nontrivial R] (δ : Derivation k R R)
    (hconstants : ∀ r : R, δ r = 0 → ∃ c : k, algebraMap k R c = r) (h : H) :
    (tensorConstantsEquiv δ hconstants h : R ⊗[k] H) = (1 : R) ⊗ₜ[k] h := rfl
end StrictEUnit

#print axioms StrictEUnit.derivation_scalar_sequence_exact
#print axioms StrictEUnit.scalar_inclusion_rTensor
#print axioms StrictEUnit.tensorDerivation_constants
#print axioms StrictEUnit.tensorConstantsInclusion
#print axioms StrictEUnit.tensorDerivation_constants_unique
#print axioms StrictEUnit.tensorConstantsEquiv
#print axioms StrictEUnit.tensorConstantsEquiv_coe
