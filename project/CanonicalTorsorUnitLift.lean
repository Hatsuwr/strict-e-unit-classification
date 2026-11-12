import CanonicalTorsor
import FlatRegularChartLift
import LaurentLogBase

/-!
# Character lifting from the canonical torsor map

No equivariant charts are supplied as premises. They are constructed from
bijectivity of the canonical torsor map; their equivariance follows from
coassociativity of the given coaction. Faithful flatness and canonical-map
bijectivity remain genuine torsor hypotheses, not facts established for the
manuscript's PV ring.
-/
open TensorProduct
open scoped TensorProduct
noncomputable section
namespace StrictEUnit

section General
variable {B R H : Type*} [CommRing B] [IsDomain B] [UniqueFactorizationMonoid B]
  [CommRing R] [IsDomain R] [Algebra B R]
  [CommRing H] [Bialgebra B H]

/-- A grouplike unit of a commutative bialgebra lifts to a regular weighted
unit on any domain algebra with the indicated faithfully flat canonical
torsor map. Coaction counitality is not required for this implication;
standard coassociativity is sufficient for the constructed chart equations. -/
theorem exists_character_unit_of_canonical_torsor
    [Module.FaithfullyFlat B R]
    (ρ : R →ₐ[B] R ⊗[B] H)
    (hcan : Function.Bijective (torsorCanonical ρ))
    (hcoassoc : ∀ s : R,
      Algebra.TensorProduct.assoc B R H H
        (Algebra.TensorProduct.map ρ (AlgHom.id B H) (ρ s)) =
      weightBaseChangeAlgHom R (Bialgebra.comulAlgHom B H) (ρ s))
    (χ : Hˣ)
    (hχ : Coalgebra.comul (R := B) (χ : H) = (χ : H) ⊗ₜ[B] (χ : H)) :
    ∃ v w : R, ρ v = v ⊗ₜ[B] (χ : H) ∧
      ρ w = w ⊗ₜ[B] (↑χ⁻¹ : H) ∧ v * w = 1 ∧ IsUnit v := by
  let ι : R →ₐ[B] R ⊗[B] H := Algebra.TensorProduct.includeLeft
  let ψ : (R ⊗[B] H)ˣ :=
    Units.map (Algebra.TensorProduct.includeRight : H →ₐ[B] R ⊗[B] H).toMonoidHom χ
  let e := torsorCanonicalEquiv ρ hcan
  obtain ⟨v, w, hv, hw, hvw, hunit⟩ :=
    exists_character_unit_of_flat_regular_chart B H R ρ ι ψ χ hχ e
      (torsorTargetChart e) (torsorCanonicalEquiv_coaction ρ hcan hcoassoc)
      (torsorTargetChart_includeLeft e) (torsorTargetChart_multiplier e (χ : H))
  refine ⟨v, w, ?_, ?_, hvw, hunit⟩
  · change ρ v = (v ⊗ₜ[B] (1 : H)) * ((1 : R) ⊗ₜ[B] (χ : H)) at hv
    simpa only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] using hv
  · change ρ w = (w ⊗ₜ[B] (1 : H)) * ((1 : R) ⊗ₜ[B] (↑χ⁻¹ : H)) at hw
    simpa only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] using hw

end General

section Laurent

/-- The scalar-tower law is proved explicitly to avoid the polynomial
semiring-instance inference ambiguity at this concrete base. -/
theorem laurentLogBase_self_scalar_tower (k R : Type*) [Field k] [CommRing R]
    [Algebra (LaurentLogBase k) R] :
    IsScalarTower (LaurentLogBase k) (LaurentLogBase k) R := by
  constructor
  intro a b x
  change (a * b) • x = a • b • x
  exact mul_smul a b x

attribute [local instance] laurentLogBase_self_scalar_tower
attribute [-instance] Polynomial.commSemiring in

/-- The canonical-torsor implication over the manuscript's abstract base.
The bialgebra here is over that base; identifying it with the scalar extension
of the constant-field group algebra remains a separate application step. -/
theorem exists_character_unit_of_canonical_laurent_log_torsor
    (k : Type*) [Field k]
    {R H : Type*} [CommRing R] [IsDomain R] [Algebra (LaurentLogBase k) R]
    [CommRing H] [Bialgebra (LaurentLogBase k) H]
    [Module.FaithfullyFlat (LaurentLogBase k) R]
    (ρ : R →ₐ[LaurentLogBase k] R ⊗[LaurentLogBase k] H)
    (hcan : Function.Bijective (torsorCanonical ρ))
    (hcoassoc : ∀ s : R,
      Algebra.TensorProduct.assoc (LaurentLogBase k) R H H
        (Algebra.TensorProduct.map (R := LaurentLogBase k) (S := LaurentLogBase k) ρ (AlgHom.id (LaurentLogBase k) H) (ρ s)) =
      weightBaseChangeAlgHom R (Bialgebra.comulAlgHom (LaurentLogBase k) H) (ρ s))
    (χ : Hˣ)
    (hχ : Coalgebra.comul (R := LaurentLogBase k) (χ : H) =
      (χ : H) ⊗ₜ[LaurentLogBase k] (χ : H)) :
    ∃ v w : R, ρ v = v ⊗ₜ[LaurentLogBase k] (χ : H) ∧
      ρ w = w ⊗ₜ[LaurentLogBase k] (↑χ⁻¹ : H) ∧ v * w = 1 ∧ IsUnit v := by
  letI := laurentLogBase_isDomain k
  letI := laurentLogBase_uniqueFactorizationMonoid k
  exact exists_character_unit_of_canonical_torsor ρ hcan hcoassoc χ hχ

end Laurent
end StrictEUnit
#print axioms StrictEUnit.exists_character_unit_of_canonical_torsor

#print axioms StrictEUnit.exists_character_unit_of_canonical_laurent_log_torsor

#print axioms StrictEUnit.laurentLogBase_self_scalar_tower
