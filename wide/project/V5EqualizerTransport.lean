import Mathlib.Algebra.Algebra.Subalgebra.Basic

noncomputable section
namespace StrictEUnit
variable {A X Y X' Y' : Type*} [CommSemiring A]
  [Semiring X] [Semiring Y] [Semiring X'] [Semiring Y']
  [Algebra A X] [Algebra A Y] [Algebra A X'] [Algebra A Y']

/-- Transport the algebra equalizer of two maps along compatible
source and target chart equivalences. -/
def v5EqualizerTransport
    (e : X ≃ₐ[A] X') (E : Y ≃ₐ[A] Y')
    (f g : X →ₐ[A] Y) (f' g' : X' →ₐ[A] Y')
    (hf : ∀ x, E (f x) = f' (e x)) (hg : ∀ x, E (g x) = g' (e x)) :
    AlgHom.equalizer f g ≃ₐ[A] AlgHom.equalizer f' g' := by
  let m : AlgHom.equalizer f g →ₐ[A] AlgHom.equalizer f' g' :=
    (e.toAlgHom.comp (AlgHom.equalizer f g).val).codRestrict _ (fun x => by
      change f' (e x.val) = g' (e x.val)
      rw [← hf, ← hg]
      exact congrArg E x.property)
  refine AlgEquiv.ofBijective m ⟨?_, ?_⟩
  · intro x y h
    exact Subtype.ext (e.injective (congrArg Subtype.val h))
  · intro z
    let x := e.symm z.val
    have hx : e x = z.val := e.apply_symm_apply _
    have hp : f x = g x := by
      apply E.injective
      rw [hf, hg, hx]
      exact z.property
    exact ⟨⟨x, hp⟩, Subtype.ext hx⟩

@[simp] theorem v5EqualizerTransport_apply
    (e : X ≃ₐ[A] X') (E : Y ≃ₐ[A] Y')
    (f g : X →ₐ[A] Y) (f' g' : X' →ₐ[A] Y')
    (hf : ∀ x, E (f x) = f' (e x)) (hg : ∀ x, E (g x) = g' (e x))
    (x : AlgHom.equalizer f g) :
    (v5EqualizerTransport e E f g f' g' hf hg x).val = e x.val :=
  rfl

end StrictEUnit
#print axioms StrictEUnit.v5EqualizerTransport
#print axioms StrictEUnit.v5EqualizerTransport_apply
