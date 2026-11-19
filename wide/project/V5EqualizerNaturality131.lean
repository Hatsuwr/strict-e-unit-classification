import V5SplitEqualizerDescent
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
variable {B k A R T H V : Type*}
  [CommRing B] [Field k] [CommRing A] [CommRing R] [CommRing T] [CommRing H] [CommRing V]
  [Algebra B A] [Algebra B R] [Algebra B T] [Algebra k A] [Algebra k H] [Algebra k V]
  [Module.Flat B A]

def v5EqualizerTensorChart131
    (f g : R →ₐ[B] T) (φ ψ : H →ₐ[k] V)
    (e : A ⊗[B] R ≃ₐ[A] A ⊗[k] H) (E : A ⊗[B] T ≃ₐ[A] A ⊗[k] V)
    (hf : ∀ x, E (Algebra.TensorProduct.map (AlgHom.id A A) f x) =
      Algebra.TensorProduct.map (AlgHom.id A A) φ (e x))
    (hg : ∀ x, E (Algebra.TensorProduct.map (AlgHom.id A A) g x) =
      Algebra.TensorProduct.map (AlgHom.id A A) ψ (e x)) :=
  (AlgHom.tensorEqualizerEquiv A A f g).trans
    ((v5EqualizerTransport e E _ _ _ _ hf hg).trans
      (AlgHom.tensorEqualizerEquiv A A φ ψ).symm)

theorem v5EqualizerTensorChart131_natural
    (f g : R →ₐ[B] T) (φ ψ : H →ₐ[k] V)
    (e : A ⊗[B] R ≃ₐ[A] A ⊗[k] H) (E : A ⊗[B] T ≃ₐ[A] A ⊗[k] V)
    (hf : ∀ x, E (Algebra.TensorProduct.map (AlgHom.id A A) f x) =
      Algebra.TensorProduct.map (AlgHom.id A A) φ (e x))
    (hg : ∀ x, E (Algebra.TensorProduct.map (AlgHom.id A A) g x) =
      Algebra.TensorProduct.map (AlgHom.id A A) ψ (e x))
    (x : A ⊗[B] AlgHom.equalizer f g) :
    Algebra.TensorProduct.map (AlgHom.id A A) (AlgHom.equalizer φ ψ).val
      (v5EqualizerTensorChart131 f g φ ψ e E hf hg x) =
    e (Algebra.TensorProduct.map (AlgHom.id A A) (AlgHom.equalizer f g).val x) := by
  have h := (AlgHom.tensorEqualizerEquiv A A φ ψ).apply_symm_apply
    (v5EqualizerTransport e E _ _ _ _ hf hg (AlgHom.tensorEqualizerEquiv A A f g x))
  have hv := congrArg Subtype.val h
  simpa only [v5EqualizerTensorChart131, AlgEquiv.trans_apply,
    AlgHom.tensorEqualizerEquiv_apply, AlgHom.coe_tensorEqualizer,
    v5EqualizerTransport_apply] using hv
/-- The exact right-factor normalization before the component product is
introduced. This avoids unfolding either tensor equalizer equivalence. -/
theorem v5EqualizerTensorChart131_right
    (f g : R →ₐ[B] T) (φ ψ : H →ₐ[k] V)
    (e : A ⊗[B] R ≃ₐ[A] A ⊗[k] H) (E : A ⊗[B] T ≃ₐ[A] A ⊗[k] V)
    (hf : ∀ x, E (Algebra.TensorProduct.map (AlgHom.id A A) f x) =
      Algebra.TensorProduct.map (AlgHom.id A A) φ (e x))
    (hg : ∀ x, E (Algebra.TensorProduct.map (AlgHom.id A A) g x) =
      Algebra.TensorProduct.map (AlgHom.id A A) ψ (e x))
    (t : AlgHom.equalizer f g) :
    Algebra.TensorProduct.map (AlgHom.id A A) (AlgHom.equalizer φ ψ).val
      (v5EqualizerTensorChart131 f g φ ψ e E hf hg (1 ⊗ₜ[B] t)) =
    e (1 ⊗ₜ[B] (t : R)) := by
  simpa only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    Subalgebra.val_apply] using
    v5EqualizerTensorChart131_natural f g φ ψ e E hf hg (1 ⊗ₜ[B] t)
end StrictEUnit
#print axioms StrictEUnit.v5EqualizerTensorChart131
#print axioms StrictEUnit.v5EqualizerTensorChart131_natural

#print axioms StrictEUnit.v5EqualizerTensorChart131_right
