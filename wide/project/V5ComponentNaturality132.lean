import V5EqualizerNaturality131
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
variable {k A H N J : Type*} [CommRing k] [CommRing A] [CommRing H] [CommRing N]
  [Algebra k A] [Algebra k H] [Algebra k N] [Fintype J] [DecidableEq J]

def v5TensorComponentChart132 (C : H ≃ₐ[k] (J → N)) :
    A ⊗[k] H ≃ₐ[A] (J → A ⊗[k] N) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A) C).trans
    (Algebra.TensorProduct.piRight k A A (fun _ : J => N))

def v5TensorScalarChart132 (S : Subalgebra k H) (C₀ : S ≃ₐ[k] (J → k)) :
    A ⊗[k] S ≃ₐ[A] (J → A) :=
  (v5TensorComponentChart132 C₀).trans
    (AlgEquiv.piCongrRight (fun _ : J => Algebra.TensorProduct.rid k A A))

theorem v5TensorComponentChart132_fixed
    (S : Subalgebra k H) (C : H ≃ₐ[k] (J → N)) (C₀ : S ≃ₐ[k] (J → k))
    (hc : ∀ s : S, ∀ j, C s j = algebraMap k N (C₀ s j))
    (y : A ⊗[k] S) (j : J) :
    v5TensorComponentChart132 C
      (Algebra.TensorProduct.map (AlgHom.id A A) S.val y) j =
      (v5TensorScalarChart132 S C₀ y j) ⊗ₜ[k] (1 : N) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a s =>
    change a ⊗ₜ[k] C (s : H) j = (C₀ s j • a) ⊗ₜ[k] (1 : N)
    rw [hc]
    simp [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul]
  | add x y hx hy => simp only [map_add, Pi.add_apply, TensorProduct.add_tmul, hx, hy]
end StrictEUnit
#print axioms StrictEUnit.v5TensorComponentChart132
#print axioms StrictEUnit.v5TensorScalarChart132
#print axioms StrictEUnit.v5TensorComponentChart132_fixed

namespace StrictEUnit
variable {B k A R T H V N J : Type*}
  [CommRing B] [Field k] [CommRing A] [CommRing R] [CommRing T] [CommRing H] [CommRing V]
  [CommRing N] [Algebra k N] [Fintype J] [DecidableEq J]
  [Algebra B A] [Algebra B R] [Algebra B T] [Algebra k A] [Algebra k H] [Algebra k V]
  [Module.Flat B A]

/-- The right-coordinate hypothesis for the relative chart follows from
verified equalizer squares and the scalar description of fixed components. -/
theorem v5SplitEqualizerRightCoordinate132
    (f g : R →ₐ[B] T) (φ ψ : H →ₐ[k] V)
    (e : A ⊗[B] R ≃ₐ[A] A ⊗[k] H) (E : A ⊗[B] T ≃ₐ[A] A ⊗[k] V)
    (hf : ∀ x, E (Algebra.TensorProduct.map (AlgHom.id A A) f x) =
      Algebra.TensorProduct.map (AlgHom.id A A) φ (e x))
    (hg : ∀ x, E (Algebra.TensorProduct.map (AlgHom.id A A) g x) =
      Algebra.TensorProduct.map (AlgHom.id A A) ψ (e x))
    (C : H ≃ₐ[k] (J → N)) (C₀ : AlgHom.equalizer φ ψ ≃ₐ[k] (J → k))
    (hc : ∀ s : AlgHom.equalizer φ ψ, ∀ j, C s j = algebraMap k N (C₀ s j))
    (t : AlgHom.equalizer f g) (j : J) :
    (e.trans (v5TensorComponentChart132 C)) (1 ⊗ₜ[B] (t : R)) j =
      ((v5EqualizerTensorChart131 f g φ ψ e E hf hg).trans
        (v5TensorScalarChart132 (AlgHom.equalizer φ ψ) C₀))
          (1 ⊗ₜ[B] t) j ⊗ₜ[k] (1 : N) := by
  simp only [AlgEquiv.trans_apply]
  rw [← v5EqualizerTensorChart131_right f g φ ψ e E hf hg t]
  exact v5TensorComponentChart132_fixed (AlgHom.equalizer φ ψ) C C₀ hc _ j
end StrictEUnit
#print axioms StrictEUnit.v5SplitEqualizerRightCoordinate132
