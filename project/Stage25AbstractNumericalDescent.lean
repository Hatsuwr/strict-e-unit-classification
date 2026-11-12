import Mathlib.Algebra.Field.Subfield.Basic
import Stage22NumericalUnitPreimage
import ArithmeticRecovery

/-! Abstract inverse-value descent. The source ring remains a type parameter
while the actual source-unit witness is eliminated. -/
noncomputable section
namespace StrictEUnit

/-- Unit classification transfers to two reciprocal values in an injective
algebra image, without an assumption of functional reciprocals. -/
theorem stage25_abstract_inverseValues_descent
    (k : Subfield ℂ) {R : Type*} [CommRing R] [Algebra k R]
    (ξ : R →ₐ[k] ℂ) (hξ : Function.Injective ξ)
    (hclass : ∀ v : Rˣ, HasExponentialForm k (ξ (v : R)))
    (u : ℂ) (hu : u ≠ 0) (ha : ∃ a : R, ξ a = u) (hb : ∃ b : R, ξ b = u⁻¹) :
    HasExponentialForm k u := by
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, hb⟩ := hb
  obtain ⟨v, hv, he⟩ := unit_preimage_of_injective_evaluation ξ.toRingHom hξ a b
    (by change ξ a * ξ b = 1; rw [ha, hb]; exact mul_inv_cancel₀ hu)
  have hval : ξ (v : R) = u := he.trans ha
  rw [← hval]
  exact hclass v

end StrictEUnit
#print axioms StrictEUnit.stage25_abstract_inverseValues_descent
