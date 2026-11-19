import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Maps

/-! Actual transport of derivations and differential simplicity through an algebra equivalence. -/
noncomputable section
namespace StrictEUnit
variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]

/-- Conjugate the actual linear derivation, proving its Leibniz rule. -/
def transportDerivation (e : A ≃ₐ[k] B) (D : Derivation k A A) : Derivation k B B :=
  Derivation.mk' (e.toLinearMap.comp (D.toLinearMap.comp e.symm.toLinearMap)) (by
    intro x y
    change e (D (e.symm (x * y))) = x • e (D (e.symm y)) + y • e (D (e.symm x))
    rw [map_mul, D.leibniz]
    simp only [smul_eq_mul, map_add, map_mul, e.apply_symm_apply])

@[simp] theorem transportDerivation_apply (e : A ≃ₐ[k] B)
    (D : Derivation k A A) (x : B) :
    transportDerivation e D x = e (D (e.symm x)) := rfl

/-- Differential simplicity is invariant under an actual algebra equivalence. -/
theorem stable_ideal_eq_top_transport (e : A ≃ₐ[k] B) (D : Derivation k A A)
    (hA : ∀ I : Ideal A, (∀ x ∈ I, D x ∈ I) → I ≠ ⊥ → I = ⊤)
    (J : Ideal B) (hJ : ∀ x ∈ J, transportDerivation e D x ∈ J) (hne : J ≠ ⊥) :
    J = ⊤ := by
  let I := J.comap e.toRingHom
  have hI : ∀ x ∈ I, D x ∈ I := by
    intro x hx
    have h := hJ (e x) hx
    simpa only [transportDerivation_apply, e.symm_apply_apply] using h
  have hi : I ≠ ⊥ := by
    intro hz
    apply hne
    have he := Ideal.map_comap_of_surjective e.toRingHom e.surjective J
    change I.map e.toRingHom = J at he
    rw [hz, Ideal.map_bot] at he
    exact he.symm
  have ht := hA I hI hi
  exact (Ideal.comap_eq_top_iff (f := e.toRingHom)).mp ht
end StrictEUnit
#print axioms StrictEUnit.transportDerivation
#print axioms StrictEUnit.transportDerivation_apply
#print axioms StrictEUnit.stable_ideal_eq_top_transport
