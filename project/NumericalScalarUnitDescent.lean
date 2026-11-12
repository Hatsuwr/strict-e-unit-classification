import Mathlib.Algebra.Field.Subfield.Basic
import ArithmeticRecovery
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
/-- Numerical descent from a proved scalar-unit lift over abstract algebras. -/
theorem numericalUnits_of_scalarUnitLift
    (k : Subfield ℂ) {C T : Type*} [CommRing C] [CommRing T]
    [Algebra k C] [Algebra k T]
    (η : C →ₐ[k] ℂ) (ξ : T →ₐ[k] ℂ) (ι : C →ₐ[k] T)
    (hcompat : ∀ r : C, ξ (ι r) = η r)
    (hclass : ∀ v : Cˣ, HasExponentialForm k (η (v : C)))
    (hlift : ∀ u : Tˣ, ∃ v : Cˣ, ∃ a : kˣ,
      u = Units.map (algebraMap k T).toMonoidHom a * Units.map ι.toMonoidHom v)
    (u : Tˣ) : HasExponentialForm k (ξ (u : T)) := by
  obtain ⟨v, a, hu⟩ := hlift u
  have h := congrArg (fun w : Tˣ => ξ (w : T)) hu
  change ξ (u : T) = ξ (algebraMap k T (a : k) * ι (v : C)) at h
  rw [map_mul, ξ.commutes, hcompat] at h
  rw [h]
  apply exponential_form_mul k _ (hclass v)
  refine ⟨(a : k), (a : k).property, ?_, 0, k.zero_mem, ?_⟩
  · exact_mod_cast Units.ne_zero a
  · simp only [Complex.exp_zero, mul_one]
    rfl
end StrictEUnit
#print axioms StrictEUnit.numericalUnits_of_scalarUnitLift
