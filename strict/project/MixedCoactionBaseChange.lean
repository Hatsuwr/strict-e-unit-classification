import CanonicalDifferentialCharacter
import CandidateCoaction

/-! Convert an actual mixed-base coaction to the scalar-extended target used
by the canonical character-lift theorem. No torsor law is created by transport. -/
noncomputable section
open scoped TensorProduct
set_option maxHeartbeats 200000
namespace StrictEUnit
variable {k B R H : Type*} [CommRing k] [CommRing B] [CommRing R] [CommRing H]
  [Algebra k B] [Algebra B R] [Algebra k R] [IsScalarTower k B R] [Algebra k H]

/-- Insert the scalar extension in the target using the actual tensor equivalence. -/
def scalarTargetCoaction (ρ : R →ₐ[B] R ⊗[k] H) :
    R →ₐ[B] R ⊗[B] (B ⊗[k] H) :=
  (Algebra.TensorProduct.cancelBaseChange k B B R H).symm.toAlgHom.comp ρ

@[simp] theorem constantFieldCoaction_scalarTarget (ρ : R →ₐ[B] R ⊗[k] H) (r : R) :
    constantFieldCoaction (scalarTargetCoaction ρ) r = ρ r :=
  (Algebra.TensorProduct.cancelBaseChange k B B R H).apply_symm_apply _

/-- Exact agreement of the two actual canonical maps after target transport. -/
theorem scalarTargetCoaction_canonical (ρ : R →ₐ[B] R ⊗[k] H)
    (z : R ⊗[B] R) :
    Algebra.TensorProduct.cancelBaseChange k B B R H
      (torsorCanonical (scalarTargetCoaction ρ) z) = relativeCandidateCanonical ρ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r s =>
    rw [torsorCanonical_tmul, map_mul]
    change _ * constantFieldCoaction (scalarTargetCoaction ρ) s = _
    rw [constantFieldCoaction_scalarTarget]
    simp only [Algebra.TensorProduct.one_def, Algebra.TensorProduct.cancelBaseChange_tmul,
      one_smul]
    rfl

/-- Bijectivity is transported, rather than restated as an additional premise. -/
theorem scalarTargetCoaction_canonical_bijective (ρ : R →ₐ[B] R ⊗[k] H)
    (hc : Function.Bijective (relativeCandidateCanonical ρ)) :
    Function.Bijective (torsorCanonical (scalarTargetCoaction ρ)) := by
  let e := Algebra.TensorProduct.cancelBaseChange k B B R H
  constructor
  · intro x y h
    apply hc.injective
    rw [← scalarTargetCoaction_canonical ρ x, ← scalarTargetCoaction_canonical ρ y, h]
  · intro y
    obtain ⟨x,hx⟩ := hc.surjective (e y)
    refine ⟨x,e.injective ?_⟩
    rw [scalarTargetCoaction_canonical, hx]

/-- A weight equation is literally preserved by the target reassociation. -/
theorem scalarTargetCoaction_weight_iff (ρ : R →ₐ[B] R ⊗[k] H) (r : R) (h : H) :
    scalarTargetCoaction ρ r = r ⊗ₜ[B] ((1:B) ⊗ₜ[k] h) ↔
      ρ r = r ⊗ₜ[k] h := by
  constructor
  · intro hr
    have he := congrArg (Algebra.TensorProduct.cancelBaseChange k B B R H) hr
    change constantFieldCoaction (scalarTargetCoaction ρ) r = _ at he
    simpa only [constantFieldCoaction_scalarTarget,
      Algebra.TensorProduct.cancelBaseChange_tmul, one_smul] using he
  · intro hr
    apply (Algebra.TensorProduct.cancelBaseChange k B B R H).injective
    change constantFieldCoaction (scalarTargetCoaction ρ) r = _
    rw [constantFieldCoaction_scalarTarget, hr,
      Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]
end StrictEUnit
#print axioms StrictEUnit.scalarTargetCoaction
#print axioms StrictEUnit.constantFieldCoaction_scalarTarget
#print axioms StrictEUnit.scalarTargetCoaction_canonical
#print axioms StrictEUnit.scalarTargetCoaction_canonical_bijective
#print axioms StrictEUnit.scalarTargetCoaction_weight_iff
