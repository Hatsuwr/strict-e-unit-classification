import V5MixedComparisonSurjectivity
import PVConstantInjectivity

open scoped TensorProduct
open TensorProduct
noncomputable section
namespace StrictEUnit
variable {k B R S E : Type*} [Field k] [CommRing B] [CommRing R] [CommRing S] [Field E]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
  [Algebra k S] [Algebra B S] [IsScalarTower k B S]
  [Algebra k E] [Algebra B E] [IsScalarTower k B E]

theorem v5_mixedDerivative_map_left
    (dB : Derivation k B B) (dR : Derivation k R R)
    (dS : Derivation k S S) (dE : Derivation k E E)
    (hR : ∀ b, dR (algebraMap B R b) = algebraMap B R (dB b))
    (hS : ∀ b, dS (algebraMap B S b) = algebraMap B S (dB b))
    (hE : ∀ b, dE (algebraMap B E b) = algebraMap B E (dB b))
    (f : R →ₐ[B] E) (hfD : ∀ r, dE (f r) = f (dR r))
    (z : R ⊗[B] S) :
    mixedRelativeTensorDerivation dB dE dS hE hS
      (Algebra.TensorProduct.map f (AlgHom.id B S) z) =
    Algebra.TensorProduct.map f (AlgHom.id B S)
      (mixedRelativeTensorDerivation dB dR dS hR hS z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r s =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      mixedRelativeTensorDerivation_tmul, map_add, hfD]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Mixed constant multiplication is injective. The flat module here is S,
not the PV candidate R. All field and differential hypotheses are explicit. -/
theorem v5_mixedConstantMultiplication_injective [Module.Flat B S]
    (dB : Derivation k B B) (dR : Derivation k R R) (dS : Derivation k S S)
    (hR : ∀ b, dR (algebraMap B R b) = algebraMap B R (dB b))
    (hS : ∀ b, dS (algebraMap B S b) = algebraMap B S (dB b))
    (dE : Derivation k E E) (f : R →ₐ[B] E) (hf : Function.Injective f)
    (hfD : ∀ r, dE (f r) = f (dR r))
    (hconstants : ∀ a, dE a = 0 → ∃ c : k, algebraMap k E c = a) :
    Function.Injective
      (v5MixedConstantMultiplication (mixedRelativeTensorDerivation dB dR dS hR hS)) := by
  have hE : ∀ b, dE (algebraMap B E b) = algebraMap B E (dB b) := by
    intro b
    rw [← f.commutes, hfD, hR, f.commutes]
  let τ : R ⊗[B] S →ₐ[k] E ⊗[B] S :=
    (Algebra.TensorProduct.map f (AlgHom.id B S)).restrictScalars k
  have hτ : Function.Injective τ :=
    Module.Flat.rTensor_preserves_injective_linearMap f.toLinearMap hf
  let d := mixedRelativeTensorDerivation dB dR dS hR hS
  let dT := mixedRelativeTensorDerivation dB dE dS hE hS
  apply constant_multiplication_injective_of_localization
    (f.restrictScalars k) hf τ hτ
    (fun r => ?_) dE dT (fun a => ?_) hconstants
    (derivationConstants d) (fun h => ?_)
    ((v5MixedConstantMultiplication d).toLinearMap.restrictScalars k)
    (fun r h => ?_)
  · change Algebra.TensorProduct.map f (AlgHom.id B S) (r ⊗ₜ[B] (1:S)) =
      f r ⊗ₜ[B] (1:S)
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  · change mixedRelativeTensorDerivation dB dE dS hE hS (a ⊗ₜ[B] (1:S)) =
      dE a ⊗ₜ[B] (1:S)
    rw [mixedRelativeTensorDerivation_tmul, dS.map_one_eq_zero, tmul_zero, add_zero]
  · change mixedRelativeTensorDerivation dB dE dS hE hS
      (Algebra.TensorProduct.map f (AlgHom.id B S) (h : R ⊗[B] S)) = 0
    rw [v5_mixedDerivative_map_left dB dR dS dE hR hS hE f hfD,
      show mixedRelativeTensorDerivation dB dR dS hR hS (h : R ⊗[B] S) = 0
        from h.property, map_zero]
  · rfl

end StrictEUnit
#print axioms StrictEUnit.v5_mixedDerivative_map_left
#print axioms StrictEUnit.v5_mixedConstantMultiplication_injective
