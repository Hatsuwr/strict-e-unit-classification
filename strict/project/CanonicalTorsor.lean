import TorsorChartTarget
import Mathlib.RingTheory.Bialgebra.Basic

/-!
The canonical map of an affine algebraic torsor is constructed from its
coaction. Bijectivity is an explicit torsor hypothesis, not proved for a
particular Picard–Vessiot ring here.
-/
open scoped TensorProduct
open TensorProduct
noncomputable section
namespace StrictEUnit
section General
variable {B R H : Type*} [CommRing B] [CommRing R] [CommRing H]
  [Algebra B R] [Algebra B H]

/-- The actual canonical map r tensor s ↦ (r tensor 1) ρ(s). -/
def torsorCanonical (ρ : R →ₐ[B] R ⊗[B] H) :
    R ⊗[B] R →ₐ[R] R ⊗[B] H :=
  Algebra.TensorProduct.lift (Algebra.ofId R (R ⊗[B] H)) ρ
    (fun _ _ => Commute.all _ _)

@[simp] theorem torsorCanonical_tmul (ρ : R →ₐ[B] R ⊗[B] H) (r s : R) :
    torsorCanonical ρ (r ⊗ₜ[B] s) = (r ⊗ₜ[B] (1 : H)) * ρ s := rfl

/-- The torsor bijectivity axiom supplies an actual R-algebra chart. -/
def torsorCanonicalEquiv (ρ : R →ₐ[B] R ⊗[B] H)
    (hcan : Function.Bijective (torsorCanonical ρ)) :
    R ⊗[B] R ≃ₐ[R] R ⊗[B] H :=
  AlgEquiv.ofBijective (torsorCanonical ρ) hcan

@[simp] theorem torsorCanonicalEquiv_apply (ρ : R →ₐ[B] R ⊗[B] H)
    (hcan : Function.Bijective (torsorCanonical ρ)) (z : R ⊗[B] R) :
    torsorCanonicalEquiv ρ hcan z = torsorCanonical ρ z := rfl

@[simp] theorem torsorCanonicalEquiv_tmul (ρ : R →ₐ[B] R ⊗[B] H)
    (hcan : Function.Bijective (torsorCanonical ρ)) (r s : R) :
    torsorCanonicalEquiv ρ hcan (r ⊗ₜ[B] s) =
      (r ⊗ₜ[B] (1 : H)) * ρ s := rfl

/-- The target chart on the second tensor factor is the actual twice-applied
coaction, with the standard associator. -/
theorem torsorTargetChart_one_tmul
    (ρ : R →ₐ[B] R ⊗[B] H)
    (hcan : Function.Bijective (torsorCanonical ρ)) (z : R ⊗[B] H) :
    torsorTargetChart (torsorCanonicalEquiv ρ hcan) ((1 : R) ⊗ₜ[B] z) =
      Algebra.TensorProduct.assoc B R H H
        (Algebra.TensorProduct.map ρ (AlgHom.id B H) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s h =>
    rw [torsorTargetChart_tmul, torsorCanonicalEquiv_tmul]
    simp only [← Algebra.TensorProduct.one_def, one_mul,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]

end General
section Coaction
variable {B R H : Type*} [CommRing B] [CommRing R] [CommRing H]
  [Algebra B R] [Bialgebra B H]

/-- Standard coassociativity implies equivariance of the canonical chart.
The coassociativity premise is stated with the original coaction, not the
chart or its induced weight spaces. -/
theorem torsorCanonicalEquiv_coaction
    (ρ : R →ₐ[B] R ⊗[B] H)
    (hcan : Function.Bijective (torsorCanonical ρ))
    (hcoassoc : ∀ s : R,
      Algebra.TensorProduct.assoc B R H H
        (Algebra.TensorProduct.map ρ (AlgHom.id B H) (ρ s)) =
      weightBaseChangeAlgHom R (Bialgebra.comulAlgHom B H) (ρ s))
    (z : R ⊗[B] R) :
    torsorTargetChart (torsorCanonicalEquiv ρ hcan)
      (weightBaseChangeAlgHom R ρ z) =
    weightBaseChangeAlgHom R (Bialgebra.comulAlgHom B H)
      (torsorCanonicalEquiv ρ hcan z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r s =>
    rw [weightBaseChangeAlgHom_tmul, torsorCanonicalEquiv_tmul]
    have ht : r ⊗ₜ[B] ρ s = r • ((1 : R) ⊗ₜ[B] ρ s) := by
      rw [smul_tmul', smul_eq_mul, mul_one]
    rw [ht, map_smul, torsorTargetChart_one_tmul, hcoassoc]
    have hm : (r ⊗ₜ[B] (1 : H)) * ρ s = r • ρ s :=
      (Algebra.smul_def r (ρ s)).symm
    rw [hm, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]
end Coaction

end StrictEUnit

#print axioms StrictEUnit.torsorCanonical
#print axioms StrictEUnit.torsorCanonical_tmul
#print axioms StrictEUnit.torsorCanonicalEquiv
#print axioms StrictEUnit.torsorCanonicalEquiv_apply
#print axioms StrictEUnit.torsorCanonicalEquiv_tmul


#print axioms StrictEUnit.torsorTargetChart_one_tmul
#print axioms StrictEUnit.torsorCanonicalEquiv_coaction
