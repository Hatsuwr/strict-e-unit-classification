import Mathlib.Algebra.Algebra.Equiv
noncomputable section
namespace StrictEUnit
variable {k C Q L : Type*} [CommSemiring k] [CommRing C] [CommRing Q] [CommRing L]
  [Algebra k C] [Algebra k Q] [Algebra k L]
def v5TransportEvaluation (e : C ≃ₐ[k] Q) (ev : Q →ₐ[k] L) : C →ₐ[k] L :=
  ev.comp e.toAlgHom

def v5UnitTransport (e : C ≃ₐ[k] Q) (u : Qˣ) : Cˣ :=
  Units.map e.symm.toMonoidHom u

theorem v5UnitTransport_value (e : C ≃ₐ[k] Q) (ev : Q →ₐ[k] L) (u : Qˣ) :
    ev (e (v5UnitTransport e u).val) = ev u.val := by
  change ev (e (e.symm u.val)) = _
  rw [AlgEquiv.apply_symm_apply]

theorem v5UnitTransport_inverse_value (e : C ≃ₐ[k] Q) (ev : Q →ₐ[k] L) (u : Qˣ) :
    ev (e (v5UnitTransport e u).inv) = ev u.inv := by
  change ev (e (e.symm u.inv)) = _
  rw [AlgEquiv.apply_symm_apply]

theorem v5UnitTransport_exists (e : C ≃ₐ[k] Q) (ev : Q →ₐ[k] L) (u : Qˣ)
    (a b : L) (ha : ev u.val = a) (hb : ev u.inv = b) :
    ∃ v : Cˣ, ev (e v.val) = a ∧ ev (e v.inv) = b :=
  ⟨v5UnitTransport e u, (v5UnitTransport_value e ev u).trans ha,
    (v5UnitTransport_inverse_value e ev u).trans hb⟩
end StrictEUnit
#print axioms StrictEUnit.v5UnitTransport
#print axioms StrictEUnit.v5UnitTransport_value
#print axioms StrictEUnit.v5UnitTransport_inverse_value

#print axioms StrictEUnit.v5TransportEvaluation

#print axioms StrictEUnit.v5UnitTransport_exists
