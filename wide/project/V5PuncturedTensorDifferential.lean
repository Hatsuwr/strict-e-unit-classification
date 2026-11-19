import V5PuncturedKummerDerivative
import Mathlib.RingTheory.TensorProduct.Basic

noncomputable section
open scoped TensorProduct
namespace StrictEUnit

/-- Euler derivative specified by actual complex differentiation off zero. -/
def V5HasPuncturedEuler (f g : V5PuncturedFunctions) : Prop :=
  V5HasPuncturedDeriv f (fun z => g z / (z : ℂ))

theorem V5HasPuncturedEuler.zero : V5HasPuncturedEuler 0 0 := by
  simpa [V5HasPuncturedEuler] using V5HasPuncturedDeriv.const 0

theorem V5HasPuncturedEuler.add {f df g dg : V5PuncturedFunctions}
    (hf : V5HasPuncturedEuler f df) (hg : V5HasPuncturedEuler g dg) :
    V5HasPuncturedEuler (f+g) (df+dg) := by
  simpa only [V5HasPuncturedEuler, Pi.add_apply, add_div] using V5HasPuncturedDeriv.add hf hg

theorem V5HasPuncturedEuler.mul {f df g dg : V5PuncturedFunctions}
    (hf : V5HasPuncturedEuler f df) (hg : V5HasPuncturedEuler g dg) :
    V5HasPuncturedEuler (f*g) (df*g+f*dg) := by
  have hh := V5HasPuncturedDeriv.mul hf hg
  have he : (fun z : ℂˣ => df z / (z : ℂ)) * g + f * (fun z => dg z / (z : ℂ)) =
      (fun z => (df*g+f*dg) z / (z : ℂ)) := by
    funext z
    simp only [Pi.add_apply, Pi.mul_apply]
    ring
  change V5HasPuncturedDeriv (f*g) _
  rw [he] at hh
  exact hh

/-- Transport an actual Euler rule through any compatible tensor realization.
Only additive pure-tensor rules are used, so this applies directly to the
underlying additive map of a constructed tensor derivation. -/
theorem v5_punctured_tensor_euler_transport
    {B S D : Type*} [CommRing B] [CommRing S] [CommRing D]
    [Algebra B S] [Algebra B D]
    (β : S →+* V5PuncturedFunctions) (ω : D →+* V5PuncturedFunctions)
    (η : S ⊗[B] D →+* V5PuncturedFunctions)
    (δS : S →+ S) (δD : D →+ D) (Δ : S ⊗[B] D →+ S ⊗[B] D)
    (hη : ∀ s d, η (s ⊗ₜ[B] d) = β s * ω d)
    (hΔ : ∀ s d, Δ (s ⊗ₜ[B] d) = δS s ⊗ₜ[B] d + s ⊗ₜ[B] δD d)
    (hS : ∀ s, V5HasPuncturedEuler (β s) (β (δS s)))
    (hD : ∀ d, V5HasPuncturedEuler (ω d) (ω (δD d))) :
    ∀ x, V5HasPuncturedEuler (η x) (η (Δ x)) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using V5HasPuncturedEuler.zero
  | tmul s d =>
    rw [hΔ, map_add, hη, hη, hη]
    exact (hS s).mul (hD d)
  | add x y hx hy =>
    simpa only [map_add] using hx.add hy

/-- The Euler chain rule has exact Kummer weight q, including q=0. -/
theorem V5HasPuncturedEuler.kummer_pullback {f df : V5PuncturedFunctions}
    (hf : V5HasPuncturedEuler f df) (q : ℕ) :
    V5HasPuncturedEuler (fun z => f (z^q)) (fun z => (q : ℂ) * df (z^q)) := by
  have hh := V5HasPuncturedDeriv.kummer_pullback hf q
  have he : (fun z : ℂˣ => ((q : ℂ) * (z : ℂ)^(q-1)) * (df (z^q) / ((z^q : ℂˣ) : ℂ))) =
      (fun z => ((q : ℂ) * df (z^q)) / (z : ℂ)) := by
    funext z
    apply (eq_div_iff (Units.ne_zero z)).mpr
    rw [mul_comm _ (z : ℂ), v5_punctured_kummer_euler]
    rw [mul_div_cancel₀ _ (Units.ne_zero (z^q))]
  change V5HasPuncturedDeriv _ _
  rw [he] at hh
  exact hh

def v5PuncturedPowerPullback (q : ℕ) : V5PuncturedFunctions →+* V5PuncturedFunctions where
  toFun f := fun z => f (z^q)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Differential transport for a ramified left factor and an ordinary right
factor. The tensor rule has q times the left Euler derivative, exactly as
dictated by z↦t^q; no invertibility of q is required. -/
theorem v5_kummer_punctured_tensor_euler_transport
    {B S D : Type*} [CommRing B] [CommRing S] [CommRing D]
    [Algebra B S] [Algebra B D]
    (q : ℕ) (β : S →+* V5PuncturedFunctions) (ω : D →+* V5PuncturedFunctions)
    (η : S ⊗[B] D →+* V5PuncturedFunctions)
    (δS : S →+ S) (δD : D →+ D) (Δ : S ⊗[B] D →+ S ⊗[B] D)
    (hη : ∀ s d z, η (s ⊗ₜ[B] d) z = β s (z^q) * ω d z)
    (hΔ : ∀ s d, Δ (s ⊗ₜ[B] d) = (q • δS s) ⊗ₜ[B] d + s ⊗ₜ[B] δD d)
    (hS : ∀ s, V5HasPuncturedEuler (β s) (β (δS s)))
    (hD : ∀ d, V5HasPuncturedEuler (ω d) (ω (δD d))) :
    ∀ x, V5HasPuncturedEuler (η x) (η (Δ x)) := by
  apply v5_punctured_tensor_euler_transport ((v5PuncturedPowerPullback q).comp β) ω η
    (q • δS) δD Δ
  · intro s d
    funext z
    exact hη s d z
  · exact hΔ
  · intro s
    have hh := (hS s).kummer_pullback q
    have he : ((v5PuncturedPowerPullback q).comp β) ((q • δS) s) =
        (fun z => (q : ℂ) * β (δS s) (z^q)) := by
      ext z
      change β (q • δS s) (z^q) = _
      rw [map_nsmul]
      simp only [Pi.smul_apply, nsmul_eq_mul]
    rw [he]
    exact hh
  · exact hD

/-- A formal eigenline equation becomes the literal analytic Euler ODE
for a representative on the punctured plane. -/
theorem v5_punctured_euler_eigenline
    {T : Type*} [CommRing T] (η : T →+* V5PuncturedFunctions) (Δ : T →+ T)
    (hΔ : ∀ x, V5HasPuncturedEuler (η x) (η (Δ x))) (x b : T)
    (he : Δ x = b*x) :
    ∃ F : ℂ → ℂ, (∀ z : ℂˣ, F z = η x z) ∧
      ∀ z : ℂˣ, HasDerivAt F (η b z * F z / (z : ℂ)) z := by
  obtain ⟨F,hF,hd⟩ := hΔ x
  refine ⟨F,hF,?_⟩
  intro z
  simpa only [he, map_mul, Pi.mul_apply, hF z] using hd z

end StrictEUnit
#print axioms StrictEUnit.V5HasPuncturedEuler.add
#print axioms StrictEUnit.V5HasPuncturedEuler.mul
#print axioms StrictEUnit.v5_punctured_tensor_euler_transport

#print axioms StrictEUnit.V5HasPuncturedEuler.kummer_pullback
#print axioms StrictEUnit.v5_kummer_punctured_tensor_euler_transport
#print axioms StrictEUnit.v5_punctured_euler_eigenline
