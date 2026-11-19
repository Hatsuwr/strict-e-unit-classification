import WeightBaseChange

/-!
# Faithfully flat descent and flat ascent of the actual invariant submodule

These results identify the scalar comparison maps on pure tensors. Flatness
preserves the actual equalizer, and faithful flatness reflects surjectivity
and injectivity. No torsor or invariant-ring assertion is postulated here.
The local or original invariant-image hypotheses remain explicit.
-/

open scoped TensorProduct
open TensorProduct

noncomputable section
namespace StrictEUnit

variable {B R T : Type*} [CommRing B] [CommRing R] [CommRing T]
  [Algebra B R] [Algebra B T]

/-- The weight-one base-change equivalence, with `1 tensor 1` identified
with the actual unit of the tensor-product algebra. -/
def fixedSpaceBaseChangeEquiv
    (A : Type*) [CommRing A] [Algebra B A] [Module.Flat B A]
    (ρ ι : R →ₐ[B] T) :
    A ⊗[B] weightSpace ρ ι 1 ≃ₗ[A]
      weightSpace (weightBaseChangeAlgHom A ρ) (weightBaseChangeAlgHom A ι) 1 :=
  (actualWeightSpaceBaseChangeEquiv A ρ ι 1).trans
    (LinearEquiv.ofEq _ _ (by rw [← Algebra.TensorProduct.one_def]))

@[simp] theorem fixedSpaceBaseChangeEquiv_tmul
    (A : Type*) [CommRing A] [Algebra B A] [Module.Flat B A]
    (ρ ι : R →ₐ[B] T) (a : A) (x : weightSpace ρ ι 1) :
    ((fixedSpaceBaseChangeEquiv A ρ ι) (a ⊗ₜ[B] x) : A ⊗[B] R) =
      a ⊗ₜ[B] (x : R) := rfl

/-- The square comparing scalars with invariants commutes for the real
maps. Its proof reduces to the tensor balancing identity. -/
theorem tensor_scalarsToFixed_apply
    (A : Type*) [CommRing A] [Algebra B A] [Module.Flat B A]
    (ρ ι : R →ₐ[B] T) (x : A ⊗[B] B) :
    fixedSpaceBaseChangeEquiv A ρ ι ((scalarsToFixed ρ ι).lTensor A x) =
      scalarsToFixed (weightBaseChangeAlgHom A ρ) (weightBaseChangeAlgHom A ι)
        (AlgebraTensorModule.rid B A A x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
    apply Subtype.ext
    simp only [LinearMap.lTensor_tmul, fixedSpaceBaseChangeEquiv_tmul,
      scalarsToFixed_coe, AlgebraTensorModule.rid_tmul,
      Algebra.TensorProduct.algebraMap_apply]
    rw [Algebra.algebraMap_eq_smul_one]
    exact (TensorProduct.smul_tmul b a (1 : R)).symm

/-- Surjectivity of the scalar-to-invariant map is preserved and reflected
by its explicit base-change square. Faithfulness is not needed for this square. -/
theorem tensor_scalarsToFixed_surjective_iff
    (A : Type*) [CommRing A] [Algebra B A] [Module.Flat B A]
    (ρ ι : R →ₐ[B] T) :
    Function.Surjective ((scalarsToFixed ρ ι).lTensor A) ↔
      Function.Surjective
        (scalarsToFixed (weightBaseChangeAlgHom A ρ) (weightBaseChangeAlgHom A ι)) := by
  let e := fixedSpaceBaseChangeEquiv A ρ ι
  let u := AlgebraTensorModule.rid B A A
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h (e.symm y)
    refine ⟨u x, ?_⟩
    rw [← tensor_scalarsToFixed_apply, hx]
    exact e.apply_symm_apply y
  · intro h y
    obtain ⟨a, ha⟩ := h (e y)
    refine ⟨u.symm a, ?_⟩
    apply e.injective
    rw [tensor_scalarsToFixed_apply]
    simpa only [u, LinearEquiv.apply_symm_apply] using ha

/-- Injectivity obeys the same canonical comparison. -/
theorem tensor_scalarsToFixed_injective_iff
    (A : Type*) [CommRing A] [Algebra B A] [Module.Flat B A]
    (ρ ι : R →ₐ[B] T) :
    Function.Injective ((scalarsToFixed ρ ι).lTensor A) ↔
      Function.Injective
        (scalarsToFixed (weightBaseChangeAlgHom A ρ) (weightBaseChangeAlgHom A ι)) := by
  let e := fixedSpaceBaseChangeEquiv A ρ ι
  let u := AlgebraTensorModule.rid B A A
  constructor
  · intro h a b hab
    apply u.symm.injective
    apply h
    apply e.injective
    rw [tensor_scalarsToFixed_apply, tensor_scalarsToFixed_apply]
    simpa only [u, LinearEquiv.apply_symm_apply] using hab
  · intro h x y hxy
    apply u.injective
    apply h
    rw [← tensor_scalarsToFixed_apply, ← tensor_scalarsToFixed_apply, hxy]

/-- Scalar surjectivity is exactly the invariant-image statement, not a
stronger replacement assumption. -/
theorem scalarsToFixed_surjective_iff (ρ ι : R →ₐ[B] T) :
    Function.Surjective (scalarsToFixed ρ ι) ↔
      ∀ r : R, ρ r = ι r → ∃ b : B, algebraMap B R b = r := by
  constructor
  · intro h r hr
    obtain ⟨b, hb⟩ := h ⟨r, by simpa only [mem_weightSpace, mul_one] using hr⟩
    exact ⟨b, congrArg Subtype.val hb⟩
  · intro h r
    obtain ⟨b, hb⟩ := h r (by simpa only [mem_weightSpace, mul_one] using r.property)
    exact ⟨b, Subtype.ext hb⟩

/-- Scalar injectivity is exactly injectivity of the structural algebra map. -/
theorem scalarsToFixed_injective_iff (ρ ι : R →ₐ[B] T) :
    Function.Injective (scalarsToFixed ρ ι) ↔
      Function.Injective (algebraMap B R) := by
  constructor
  · intro h b c hbc
    exact h (Subtype.ext hbc)
  · intro h b c hbc
    exact h (congrArg Subtype.val hbc)

/-- Faithfully flat descent of invariants equal to the image of the base.
The local maps are the actual extended algebra maps. -/
theorem invariant_image_descends
    (A : Type*) [CommRing A] [Algebra B A] [Module.FaithfullyFlat B A]
    (ρ ι : R →ₐ[B] T)
    (hlocal : ∀ r : A ⊗[B] R,
      weightBaseChangeAlgHom A ρ r = weightBaseChangeAlgHom A ι r →
      ∃ a : A, algebraMap A (A ⊗[B] R) a = r) :
    ∀ r : R, ρ r = ι r → ∃ b : B, algebraMap B R b = r := by
  apply (scalarsToFixed_surjective_iff ρ ι).mp
  apply (Module.FaithfullyFlat.lTensor_surjective_iff_surjective B A
    (scalarsToFixed ρ ι)).mp
  apply (tensor_scalarsToFixed_surjective_iff A ρ ι).mpr
  exact (scalarsToFixed_surjective_iff _ _).mpr hlocal

/-- Injectivity of the scalar inclusion also descends from the actual cover. -/
theorem scalar_inclusion_injective_descends
    (A : Type*) [CommRing A] [Algebra B A] [Module.FaithfullyFlat B A]
    (ρ ι : R →ₐ[B] T)
    (hlocal : Function.Injective (algebraMap A (A ⊗[B] R))) :
    Function.Injective (algebraMap B R) := by
  apply (scalarsToFixed_injective_iff ρ ι).mp
  apply (Module.FaithfullyFlat.lTensor_injective_iff_injective B A
    (scalarsToFixed ρ ι)).mp
  apply (tensor_scalarsToFixed_injective_iff A ρ ι).mpr
  exact (scalarsToFixed_injective_iff _ _).mpr hlocal

/-- Flat ascent of the invariant-image assertion. -/
theorem invariant_image_ascends
    (A : Type*) [CommRing A] [Algebra B A] [Module.Flat B A]
    (ρ ι : R →ₐ[B] T)
    (hfixed : ∀ r : R, ρ r = ι r → ∃ b : B, algebraMap B R b = r) :
    ∀ r : A ⊗[B] R,
      weightBaseChangeAlgHom A ρ r = weightBaseChangeAlgHom A ι r →
      ∃ a : A, algebraMap A (A ⊗[B] R) a = r := by
  apply (scalarsToFixed_surjective_iff _ _).mp
  apply (tensor_scalarsToFixed_surjective_iff A ρ ι).mp
  exact LinearMap.lTensor_surjective A ((scalarsToFixed_surjective_iff ρ ι).mpr hfixed)

/-- Flat ascent of injectivity of the scalar inclusion. -/
theorem scalar_inclusion_injective_ascends
    (A : Type*) [CommRing A] [Algebra B A] [Module.Flat B A]
    (ρ ι : R →ₐ[B] T)
    (hinj : Function.Injective (algebraMap B R)) :
    Function.Injective (algebraMap A (A ⊗[B] R)) := by
  apply (scalarsToFixed_injective_iff
    (weightBaseChangeAlgHom A ρ) (weightBaseChangeAlgHom A ι)).mp
  apply (tensor_scalarsToFixed_injective_iff A ρ ι).mp
  exact Module.Flat.lTensor_preserves_injective_linearMap
    (scalarsToFixed ρ ι) ((scalarsToFixed_injective_iff ρ ι).mpr hinj)

/-- The resulting equivalence between the new scalar ring and actual
base-changed invariants. Both its hypotheses refer to the original ring. -/
def actualFixedScalarsEquiv_of_flat
    (A : Type*) [CommRing A] [Algebra B A] [Module.Flat B A]
    (ρ ι : R →ₐ[B] T)
    (hinj : Function.Injective (algebraMap B R))
    (hfixed : ∀ r : R, ρ r = ι r → ∃ b : B, algebraMap B R b = r) :
    A ≃ₗ[A] weightSpace (weightBaseChangeAlgHom A ρ) (weightBaseChangeAlgHom A ι) 1 :=
  scalarsFixedEquiv _ _ (scalar_inclusion_injective_ascends A ρ ι hinj)
    (invariant_image_ascends A ρ ι hfixed)

@[simp] theorem actualFixedScalarsEquiv_of_flat_coe
    (A : Type*) [CommRing A] [Algebra B A] [Module.Flat B A]
    (ρ ι : R →ₐ[B] T)
    (hinj : Function.Injective (algebraMap B R))
    (hfixed : ∀ r : R, ρ r = ι r → ∃ b : B, algebraMap B R b = r) (a : A) :
    (actualFixedScalarsEquiv_of_flat A ρ ι hinj hfixed a : A ⊗[B] R) =
      a ⊗ₜ[B] (1 : R) := rfl

end StrictEUnit

#print axioms StrictEUnit.fixedSpaceBaseChangeEquiv
#print axioms StrictEUnit.fixedSpaceBaseChangeEquiv_tmul
#print axioms StrictEUnit.tensor_scalarsToFixed_apply
#print axioms StrictEUnit.tensor_scalarsToFixed_surjective_iff
#print axioms StrictEUnit.tensor_scalarsToFixed_injective_iff
#print axioms StrictEUnit.scalarsToFixed_surjective_iff
#print axioms StrictEUnit.scalarsToFixed_injective_iff
#print axioms StrictEUnit.invariant_image_descends
#print axioms StrictEUnit.scalar_inclusion_injective_descends
#print axioms StrictEUnit.invariant_image_ascends
#print axioms StrictEUnit.scalar_inclusion_injective_ascends
#print axioms StrictEUnit.actualFixedScalarsEquiv_of_flat
#print axioms StrictEUnit.actualFixedScalarsEquiv_of_flat_coe
