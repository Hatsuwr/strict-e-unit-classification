import DifferentialConstantsIndependence
import PVConstantAlgebra
import MixedRelativeTensorDerivation
import Mathlib.RingTheory.Flat.Basic

/-! Injectivity of constant multiplication after an explicit injective
localization. Flatness and differential compatibility are retained as
visible hypotheses until supplied by the mixed tensor construction. -/
open scoped TensorProduct
open TensorProduct
noncomputable section
namespace StrictEUnit
section General
variable {k R E S T : Type*} [Field k] [CommRing R] [Field E] [CommRing S] [CommRing T]
  [Algebra k R] [Algebra k E] [Algebra k S] [Algebra k T]
  [Algebra R S] [IsScalarTower k R S] [Algebra E T] [IsScalarTower k E T]

omit [IsScalarTower k R S] in
/-- A faithful localization and differential independence prove injectivity
of the original tensor multiplication map. -/
theorem constant_multiplication_injective_of_localization
    (f : R →ₐ[k] E) (hf : Function.Injective f)
    (τ : S →ₐ[k] T) (hτ : Function.Injective τ)
    (hscalar : ∀ r, τ (algebraMap R S r) = algebraMap E T (f r))
    (dE : Derivation k E E) (dT : Derivation k T T)
    (hcomp : ∀ a, dT (algebraMap E T a) = algebraMap E T (dE a))
    (hconstants : ∀ a, dE a = 0 → ∃ c : k, algebraMap k E c = a)
    (H : Subalgebra k S) (hH : ∀ h : H, dT (τ (h:S)) = 0)
    (μ : R ⊗[k] H →ₗ[k] S)
    (hμ : ∀ r (h:H), μ (r ⊗ₜ[k] h) = algebraMap R S r * (h:S)) :
    Function.Injective μ := by
  let g : H →ₗ[k] T := τ.toLinearMap.comp H.val.toLinearMap
  let q : E ⊗[k] H →ₗ[E] T := g.liftBaseChange E
  let b := Module.Free.chooseBasis k H
  have hg : Function.Injective g := hτ.comp Subtype.val_injective
  have hbk : LinearIndependent k (fun i => g (b i)) :=
    b.linearIndependent.map' g (LinearMap.ker_eq_bot_of_injective hg)
  have hbE : LinearIndependent E (fun i => g (b i)) :=
    differential_constants_linearIndependent (dE.restrictScalars ℤ) (dT.restrictScalars ℤ)
      hcomp hconstants _ (fun i => hH (b i)) hbk
  have hq : Function.Injective q := by
    apply linearMap_injective_of_basis_image (b.baseChange E) q
    convert hbE using 1
    funext i
    simp only [Basis.baseChange_apply, q, LinearMap.liftBaseChange_tmul, one_smul]
  have hfTensor : Function.Injective (f.toLinearMap.rTensor H) :=
    Module.Flat.rTensor_preserves_injective_linearMap f.toLinearMap hf
  have hdiag : τ.toLinearMap.comp μ =
      (q.restrictScalars k).comp (f.toLinearMap.rTensor H) := by
    apply TensorProduct.ext'
    intro r h
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, hμ,
      LinearMap.restrictScalars_apply, LinearMap.rTensor_tmul, q,
      LinearMap.liftBaseChange_tmul, g, map_mul, hscalar, Algebra.smul_def]
    rfl
  intro x y hxy
  apply hfTensor
  apply hq
  have h := congrArg τ hxy
  change (τ.toLinearMap.comp μ) x = (τ.toLinearMap.comp μ) y at h
  rw [hdiag] at h
  exact h

end General
section Relative
variable {k B R E : Type*} [Field k] [CommRing B] [CommRing R] [Field E]
  [Algebra k B] [Algebra k R] [Algebra k E]
  [Algebra B R] [Algebra B E] [IsScalarTower k B R] [IsScalarTower k B E]

/-- Actual PV constant multiplication is injective when the candidate is
B-flat and embeds differentially in a field with exactly constants k.
Flatness and the constant-field input are explicit; neither the desired
injectivity nor any torsor isomorphism is assumed. -/
theorem pvConstantMultiplication_injective [Module.Flat B R]
    (dB : Derivation k B B) (dR : Derivation k R R)
    (hR : ∀ b, dR (algebraMap B R b) = algebraMap B R (dB b))
    (dE : Derivation k E E) (f : R →ₐ[B] E) (hf : Function.Injective f)
    (hfD : ∀ r, dE (f r) = f (dR r))
    (hconstants : ∀ a, dE a = 0 → ∃ c : k, algebraMap k E c = a) :
    Function.Injective (pvConstantMultiplication dB dR hR) := by
  have hE : ∀ b, dE (algebraMap B E b) = algebraMap B E (dB b) := by
    intro b
    rw [← f.commutes, hfD, hR, f.commutes]
  let τ : R ⊗[B] R →ₐ[k] E ⊗[B] R :=
    (Algebra.TensorProduct.map f (AlgHom.id B R)).restrictScalars k
  let dT := mixedRelativeTensorDerivation dB dE dR hE hR
  apply constant_multiplication_injective_of_localization
    (f.restrictScalars k) hf τ (relativeTensorMap_left_injective f hf)
    (fun r => ?_) dE dT (fun a => ?_) hconstants
    (pvConstantAlgebra dB dR hR) (fun h => ?_)
    ((pvConstantMultiplication dB dR hR).toLinearMap.restrictScalars k)
    (fun r h => ?_)
  · change Algebra.TensorProduct.map f (AlgHom.id B R) (r ⊗ₜ[B] (1:R)) =
      f r ⊗ₜ[B] (1:R)
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  · change mixedRelativeTensorDerivation dB dE dR hE hR (a ⊗ₜ[B] (1:R)) =
      dE a ⊗ₜ[B] (1:R)
    rw [mixedRelativeTensorDerivation_tmul, dR.map_one_eq_zero, tmul_zero, add_zero]
  · change mixedRelativeTensorDerivation dB dE dR hE hR
      (Algebra.TensorProduct.map f (AlgHom.id B R) (h : R ⊗[B] R)) = 0
    rw [mixedRelativeTensorDerivation_map_left dB dE dR hE hR f hfD,
      show relativeTensorDerivation dB dR hR (h : R ⊗[B] R) = 0 from h.property, map_zero]
  · exact pvConstantMultiplication_tmul dB dR hR r h

/-- Fraction-field specialization with the canonical localization map.
The explicit remaining PV inputs are B-flatness and the differential
fraction field's exact constant-field property. -/
theorem pvConstantMultiplication_injective_of_fractionField
    [Module.Flat B R] [IsDomain R] [Algebra R E] [IsFractionRing R E]
    [IsScalarTower B R E]
    (dB : Derivation k B B) (dR : Derivation k R R)
    (hR : ∀ b, dR (algebraMap B R b) = algebraMap B R (dB b))
    (dE : Derivation k E E)
    (hE : ∀ r, dE (algebraMap R E r) = algebraMap R E (dR r))
    (hconstants : ∀ a, dE a = 0 → ∃ c : k, algebraMap k E c = a) :
    Function.Injective (pvConstantMultiplication dB dR hR) :=
  pvConstantMultiplication_injective dB dR hR dE (IsScalarTower.toAlgHom B R E)
    (IsFractionRing.injective R E) hE hconstants

end Relative
end StrictEUnit

#print axioms StrictEUnit.constant_multiplication_injective_of_localization
#print axioms StrictEUnit.pvConstantMultiplication_injective
#print axioms StrictEUnit.pvConstantMultiplication_injective_of_fractionField
