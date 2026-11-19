import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-! Two independently represented reciprocal numbers yield one actual unit in
the source algebra when its evaluation is injective. This does not identify
their original function representatives as functional reciprocals. -/
noncomputable section
namespace StrictEUnit

/-- Exact evaluation turns two source representatives whose numerical product
is one into an actual source unit. -/
theorem unit_preimage_of_injective_evaluation
    {R K : Type*} [CommRing R] [CommRing K]
    (φ : R →+* K) (hφ : Function.Injective φ)
    (a b : R) (hab : φ a * φ b = 1) :
    ∃ u : Rˣ, (u : R) = a ∧ φ (u : R) = φ a := by
  have h : a * b = 1 := hφ (by rw [map_mul, map_one]; exact hab)
  obtain ⟨u, hu⟩ := (isUnit_iff_exists_inv.mpr ⟨b, h⟩ : IsUnit a)
  exact ⟨u, hu, congrArg φ hu⟩

/-- Separate membership of a number and its reciprocal in the exact image
suffices; no common entire representative is required. -/
theorem unit_preimage_of_inverse_values
    {k R K : Type*} [CommRing k] [CommRing R] [Field K]
    [Algebra k R] [Algebra k K]
    (φ : R →ₐ[k] K) (hφ : Function.Injective φ)
    (x : K) (hx : x ≠ 0) (ha : x ∈ φ.range) (hb : x⁻¹ ∈ φ.range) :
    ∃ u : Rˣ, φ (u : R) = x := by
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, hb⟩ := hb
  obtain ⟨u, hu, he⟩ := unit_preimage_of_injective_evaluation φ.toRingHom hφ a b
    (by simpa only [ha, hb] using mul_inv_cancel₀ hx)
  exact ⟨u, he.trans ha⟩

end StrictEUnit
#print axioms StrictEUnit.unit_preimage_of_injective_evaluation
#print axioms StrictEUnit.unit_preimage_of_inverse_values
