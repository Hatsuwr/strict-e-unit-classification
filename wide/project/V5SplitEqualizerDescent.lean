import V5EqualizerTransport
import V5FiniteFaithfullyFlatDescent
import V5SplitFlatUnramified
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.TensorProduct.Pi

noncomputable section
open scoped TensorProduct
namespace StrictEUnit
universe u v w w' l l' t
variable {B : Type v} {k : Type t} {A : Type u} {R : Type w} {T : Type w'}
    {H : Type l} {V : Type l'}
  [CommRing B] [Field k] [CommRing A] [CommRing R] [CommRing T] [CommRing H] [CommRing V]
  [Algebra B A] [Algebra B R] [Algebra B T] [Algebra k A] [Algebra k H] [Algebra k V]

/-- The algebra base change of an invariant equalizer is split when two
square-compatible chart equivalences identify it with the tensor extension
of scalar functions on a finite component set. Neither square is assumed
by the intended application; they encode the exact coaction data required. -/
def v5SplitEqualizerBaseChange [Module.Flat B A] {J : Type u} [Finite J]
    (f g : R →ₐ[B] T) (φ ψ : H →ₐ[k] V)
    (e : A ⊗[B] R ≃ₐ[A] A ⊗[k] H) (E : A ⊗[B] T ≃ₐ[A] A ⊗[k] V)
    (hf : ∀ x, E (Algebra.TensorProduct.map (AlgHom.id A A) f x) =
      Algebra.TensorProduct.map (AlgHom.id A A) φ (e x))
    (hg : ∀ x, E (Algebra.TensorProduct.map (AlgHom.id A A) g x) =
      Algebra.TensorProduct.map (AlgHom.id A A) ψ (e x))
    (e₀ : AlgHom.equalizer φ ψ ≃ₐ[k] (J → k)) :
    A ⊗[B] AlgHom.equalizer f g ≃ₐ[A] (J → A) := by
  classical
  letI : Fintype J := Fintype.ofFinite J
  let h := v5EqualizerTransport e E
    (Algebra.TensorProduct.map (AlgHom.id A A) f)
    (Algebra.TensorProduct.map (AlgHom.id A A) g)
    (Algebra.TensorProduct.map (AlgHom.id A A) φ)
    (Algebra.TensorProduct.map (AlgHom.id A A) ψ) hf hg
  let h₁ := AlgHom.tensorEqualizerEquiv A A f g
  let h₂ := AlgHom.tensorEqualizerEquiv A A φ ψ
  let h₃ := Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A) e₀
  let h₄ := Algebra.TensorProduct.piRight k A A (fun _ : J => k)
  let h₅ := AlgEquiv.piCongrRight (fun _ : J => Algebra.TensorProduct.rid k A A)
  exact h₁.trans (h.trans (h₂.symm.trans (h₃.trans (h₄.trans h₅))))

/-- Module finiteness, flatness and unramifiedness are all consequences
of the checked split model; only faithful flatness is needed to descend. -/
theorem v5_split_equalizer_descent [Module.FaithfullyFlat B A] {J : Type u} [Finite J]
    (f g : R →ₐ[B] T) (e : A ⊗[B] AlgHom.equalizer f g ≃ₐ[A] (J → A)) :
    Module.Finite B (AlgHom.equalizer f g) ∧ Module.Flat B (AlgHom.equalizer f g) ∧
      Algebra.Unramified B (AlgHom.equalizer f g) := by
  letI := v5_moduleFinite_of_faithfullyFlat_split e.toLinearEquiv
  exact ⟨inferInstance, v5_split_baseChange_flat e, v5_split_baseChange_unramified e⟩

end StrictEUnit
#print axioms StrictEUnit.v5SplitEqualizerBaseChange
#print axioms StrictEUnit.v5_split_equalizer_descent
