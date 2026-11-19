import FiberTensorChart
import MixedRelativeTensorDerivation
import CandidateDifferentialCoaction

open scoped TensorProduct
open TensorProduct
noncomputable section
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 40000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k B R S H : Type*} [CommRing k] [CommRing B] [CommRing R]
  [CommRing S] [CommRing H]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
  [Algebra k S] [Algebra B S] [IsScalarTower k B S] [Algebra k H]

/-- Move the constant factor outside and restore the R,S order. -/
def v5MixedCoactionShuffle :
    S ⊗[B] (R ⊗[k] H) ≃ₐ[k] (R ⊗[B] S) ⊗[k] H :=
  ((fiberMixedAssoc (k := k) (B := B) (A := S)).symm.restrictScalars k).trans
    (Algebra.TensorProduct.congr
      ((Algebra.TensorProduct.comm B S R).restrictScalars k) (AlgEquiv.refl (R := k) (A₁ := H)))

@[simp] theorem v5MixedCoactionShuffle_tmul (s : S) (r : R) (h : H) :
    v5MixedCoactionShuffle (s ⊗ₜ[B] (r ⊗ₜ[k] h)) = (r ⊗ₜ[B] s) ⊗ₜ[k] h := by
  have ht : (fiberMixedAssoc (k := k) (B := B) (A := S)).symm
      (s ⊗ₜ[B] (r ⊗ₜ[k] h)) = (s ⊗ₜ[B] r) ⊗ₜ[k] h := by
    apply (fiberMixedAssoc (k := k) (B := B) (A := S)).injective
    simp only [AlgEquiv.apply_symm_apply, fiberMixedAssoc_tmul]
  simp only [v5MixedCoactionShuffle, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
    ht]
  rfl

/-- Base-change a right coaction on R to the mixed solution algebra, without
asserting any torsor or action structure on S. -/
def v5MixedRelativeCoaction (ρ : R →ₐ[B] R ⊗[k] H) :
    (R ⊗[B] S) →ₐ[k] (R ⊗[B] S) ⊗[k] H :=
  (v5MixedCoactionShuffle (k := k) (B := B)).toAlgHom.comp
    (((Algebra.TensorProduct.map (AlgHom.id B S) ρ).restrictScalars k).comp
      ((Algebra.TensorProduct.comm B R S).restrictScalars k).toAlgHom)

@[simp] theorem v5MixedRelativeCoaction_tmul
    (ρ : R →ₐ[B] R ⊗[k] H) (r : R) (s : S) :
    v5MixedRelativeCoaction ρ (r ⊗ₜ[B] s) =
      v5MixedCoactionShuffle (s ⊗ₜ[B] ρ r) := rfl


/-- Differential compatibility of the shuffle with one varying S coordinate. -/
theorem v5MixedCoactionShuffle_differential
    (dB : Derivation k B B) (dR : Derivation k R R) (dS : Derivation k S S)
    (hR : ∀ b, dR (algebraMap B R b) = algebraMap B R (dB b))
    (hS : ∀ b, dS (algebraMap B S b) = algebraMap B S (dB b))
    (s : S) (z : R ⊗[k] H) :
    tensorDerivation (mixedRelativeTensorDerivation dB dR dS hR hS)
        (v5MixedCoactionShuffle (s ⊗ₜ[B] z)) =
      v5MixedCoactionShuffle (dS s ⊗ₜ[B] z) +
        v5MixedCoactionShuffle (s ⊗ₜ[B] tensorDerivation dR z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [tmul_zero, map_zero, add_zero]
  | add x y hx hy =>
    simp only [tmul_add, map_add, hx, hy]
    abel
  | tmul r h =>
    simp only [v5MixedCoactionShuffle_tmul, tensorDerivation_tmul,
      mixedRelativeTensorDerivation_tmul, add_tmul]
    exact add_comm _ _

/-- A differential coaction on R genuinely induces a differential map on the
mixed relative tensor product with arbitrary S. -/
theorem v5MixedRelativeCoaction_differential
    (dB : Derivation k B B) (dR : Derivation k R R) (dS : Derivation k S S)
    (hR : ∀ b, dR (algebraMap B R b) = algebraMap B R (dB b))
    (hS : ∀ b, dS (algebraMap B S b) = algebraMap B S (dB b))
    (ρ : R →ₐ[B] R ⊗[k] H)
    (hρ : ∀ r, tensorDerivation dR (ρ r) = ρ (dR r))
    (x : R ⊗[B] S) :
    tensorDerivation (mixedRelativeTensorDerivation dB dR dS hR hS)
        (v5MixedRelativeCoaction ρ x) =
      v5MixedRelativeCoaction ρ (mixedRelativeTensorDerivation dB dR dS hR hS x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r s =>
    rw [v5MixedRelativeCoaction_tmul, v5MixedCoactionShuffle_differential dB dR dS hR hS,
      hρ, mixedRelativeTensorDerivation_tmul, map_add,
      v5MixedRelativeCoaction_tmul, v5MixedRelativeCoaction_tmul]
    exact add_comm _ _


/-- Explicit coefficient formula for any chosen finite tensor expansion of rho(r). -/
theorem v5MixedRelativeCoaction_of_expansion
    (ρ : R →ₐ[B] R ⊗[k] H) (r : R) (s : S)
    {ι : Type*} (I : Finset ι) (a : ι → R) (h : ι → H)
    (hexp : ρ r = ∑ i ∈ I, a i ⊗ₜ[k] h i) :
    v5MixedRelativeCoaction ρ (r ⊗ₜ[B] s) =
      ∑ i ∈ I, (a i ⊗ₜ[B] s) ⊗ₜ[k] h i := by
  rw [v5MixedRelativeCoaction_tmul, hexp]
  simp only [tmul_sum, map_sum, v5MixedCoactionShuffle_tmul]

/-- Mixed differential map induced by the proved own-PV comparison.
Differential compatibility of its R-coaction is derived, not assumed. -/
theorem v5MixedOwnPVCoaction_differential
    (dB : Derivation k B B) (dR : Derivation k R R) (dS : Derivation k S S)
    (hR : ∀ b, dR (algebraMap B R b) = algebraMap B R (dB b))
    (hS : ∀ b, dS (algebraMap B S b) = algebraMap B S (dB b))
    (he : Function.Bijective (pvConstantMultiplication dB dR hR))
    (x : R ⊗[B] S) :
    tensorDerivation (mixedRelativeTensorDerivation dB dR dS hR hS)
        (v5MixedRelativeCoaction
          (inverseMultiplicationCoaction (AlgEquiv.ofBijective (pvConstantMultiplication dB dR hR) he)) x) =
      v5MixedRelativeCoaction
        (inverseMultiplicationCoaction (AlgEquiv.ofBijective (pvConstantMultiplication dB dR hR) he))
        (mixedRelativeTensorDerivation dB dR dS hR hS x) :=
  v5MixedRelativeCoaction_differential dB dR dS hR hS _
    (inverseMultiplicationCoaction_differential dB dR hR he) x

end StrictEUnit
#print axioms StrictEUnit.v5MixedCoactionShuffle
#print axioms StrictEUnit.v5MixedCoactionShuffle_tmul
#print axioms StrictEUnit.v5MixedRelativeCoaction
#print axioms StrictEUnit.v5MixedRelativeCoaction_tmul

#print axioms StrictEUnit.v5MixedCoactionShuffle_differential
#print axioms StrictEUnit.v5MixedRelativeCoaction_differential

#print axioms StrictEUnit.v5MixedRelativeCoaction_of_expansion
#print axioms StrictEUnit.v5MixedOwnPVCoaction_differential
