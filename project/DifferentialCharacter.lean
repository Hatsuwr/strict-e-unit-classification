import TensorDerivation
import InvariantDescent

/-! Differential compatibility is an explicit premise. The derivation is
over k, while invariants descend to the possibly larger base B. Thus B is
not incorrectly required to consist of differential constants. -/
open scoped TensorProduct
open TensorProduct
noncomputable section
namespace StrictEUnit
variable {k B R H : Type*} [CommRing k] [CommRing B] [CommRing R] [CommRing H]
  [Algebra k R] [Algebra k H] [Algebra B R] [SMulCommClass k B R]

/-- The coaction's weight equalizer is the actual semi-invariance equation. -/
theorem coaction_weight_iff (ρ : R →ₐ[B] R ⊗[k] H) (χ : H) (r : R) :
    r ∈ weightSpace ρ
      (Algebra.TensorProduct.includeLeft : R →ₐ[B] R ⊗[k] H)
      ((1 : R) ⊗ₜ[k] χ) ↔ ρ r = r ⊗ₜ[k] χ := by
  simp only [mem_weightSpace, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- A differential coaction preserves every character weight. Grouplikeness
is unnecessary for this step: the second tensor factor is constant. -/
theorem differential_coaction_preserves_weight (δ : Derivation k R R)
    (ρ : R →ₐ[B] R ⊗[k] H)
    (hδ : ∀ r, ρ (δ r) = tensorDerivation δ (ρ r))
    (χ : H) (r : R) (hr : ρ r = r ⊗ₜ[k] χ) :
    ρ (δ r) = δ r ⊗ₜ[k] χ := by
  rw [hδ, hr, tensorDerivation_tmul]

/-- The logarithmic derivative of a weighted unit is an actual invariant. -/
theorem logarithmic_derivative_invariant (δ : Derivation k R R)
    (ρ : R →ₐ[B] R ⊗[k] H)
    (hδ : ∀ r, ρ (δ r) = tensorDerivation δ (ρ r))
    (χ : Hˣ) (v : Rˣ) (hv : ρ (v : R) = (v : R) ⊗ₜ[k] (χ : H)) :
    ρ ((↑v⁻¹ : R) * δ (v : R)) =
      (Algebra.TensorProduct.includeLeft : R →ₐ[B] R ⊗[k] H)
        ((↑v⁻¹ : R) * δ (v : R)) := by
  let ψ : (R ⊗[k] H)ˣ := Units.map
    (Algebra.TensorProduct.includeRight : H →ₐ[k] R ⊗[k] H).toMonoidHom χ
  let ι : R →ₐ[B] R ⊗[k] H := Algebra.TensorProduct.includeLeft
  have hvw : (v : R) ∈ weightSpace ρ ι (ψ : R ⊗[k] H) :=
    (coaction_weight_iff ρ (χ : H) (v : R)).mpr hv
  have hdw : δ (v : R) ∈ weightSpace ρ ι (ψ : R ⊗[k] H) :=
    (coaction_weight_iff ρ (χ : H) _).mpr
      (differential_coaction_preserves_weight δ ρ hδ (χ : H) (v : R) hv)
  have hiw := inverse_unit_opposite_weight ρ ι ψ v hvw
  have hp := opposite_weight_mul_fixed ρ ι ψ ⟨δ (v : R), hdw⟩ ⟨↑v⁻¹, hiw⟩
  simpa only [mem_weightSpace, mul_one, one_mul, mul_comm, ι] using hp

/-- If the invariant image is the base, the logarithmic derivative belongs
to that base. No division in the ambient fraction field is needed. -/
theorem logarithmic_derivative_in_base (δ : Derivation k R R)
    (ρ : R →ₐ[B] R ⊗[k] H)
    (hδ : ∀ r, ρ (δ r) = tensorDerivation δ (ρ r))
    (hfixed : ∀ r, ρ r =
      (Algebra.TensorProduct.includeLeft : R →ₐ[B] R ⊗[k] H) r →
      ∃ b : B, algebraMap B R b = r)
    (χ : Hˣ) (v : Rˣ) (hv : ρ (v : R) = (v : R) ⊗ₜ[k] (χ : H)) :
    ∃ b : B, algebraMap B R b = (↑v⁻¹ : R) * δ (v : R) :=
  hfixed _ (logarithmic_derivative_invariant δ ρ hδ χ v hv)

/-- The base-membership conclusion can use actual faithfully flat descent
of invariants, rather than a global invariant-image assumption. -/
theorem logarithmic_derivative_in_base_of_faithfullyFlat
    (A : Type*) [CommRing A] [Algebra B A] [Module.FaithfullyFlat B A]
    (δ : Derivation k R R) (ρ : R →ₐ[B] R ⊗[k] H)
    (hδ : ∀ r, ρ (δ r) = tensorDerivation δ (ρ r))
    (hlocal : ∀ z : A ⊗[B] R,
      weightBaseChangeAlgHom A ρ z =
        weightBaseChangeAlgHom A
          (Algebra.TensorProduct.includeLeft : R →ₐ[B] R ⊗[k] H) z →
      ∃ a : A, algebraMap A (A ⊗[B] R) a = z)
    (χ : Hˣ) (v : Rˣ) (hv : ρ (v : R) = (v : R) ⊗ₜ[k] (χ : H)) :
    ∃ b : B, algebraMap B R b = (↑v⁻¹ : R) * δ (v : R) :=
  logarithmic_derivative_in_base δ ρ hδ
    (invariant_image_descends A ρ Algebra.TensorProduct.includeLeft hlocal) χ v hv
end StrictEUnit

#print axioms StrictEUnit.coaction_weight_iff
#print axioms StrictEUnit.differential_coaction_preserves_weight
#print axioms StrictEUnit.logarithmic_derivative_invariant
#print axioms StrictEUnit.logarithmic_derivative_in_base
#print axioms StrictEUnit.logarithmic_derivative_in_base_of_faithfullyFlat
