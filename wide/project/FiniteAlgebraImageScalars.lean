import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-! A finite algebra's image in any domain over an algebraically closed
field consists of scalars. The target need not be finite type or a field. -/
noncomputable section
namespace StrictEUnit
variable {k C B : Type*} [Field k] [IsAlgClosed k]
  [CommRing C] [Algebra k C] [Module.Finite k C]
  [CommRing B] [IsDomain B] [Algebra k B]

omit [IsAlgClosed k] [IsDomain B] in
/-- The actual image is finite as a module, by surjectivity onto the range. -/
theorem finite_algebra_hom_range (f : C →ₐ[k] B) : Module.Finite k f.range :=
  Module.Finite.of_surjective f.rangeRestrict.toLinearMap f.rangeRestrict_surjective

/-- Every image element is scalar; this uses algebraic closedness only after
passing to the genuine finite domain image. -/
theorem finite_algebra_hom_image_scalar (f : C →ₐ[k] B) (c : C) :
    ∃ a : k, algebraMap k B a = f c := by
  letI := finite_algebra_hom_range f
  obtain ⟨a, ha⟩ :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := f.range)).2
      (f.rangeRestrict c)
  exact ⟨a, congrArg (fun z : f.range => (z : B)) ha⟩

/-- The image subalgebra is exactly the scalar subalgebra. -/
theorem finite_algebra_hom_range_eq_bot (f : C →ₐ[k] B) : f.range = ⊥ := by
  apply le_antisymm ?_ bot_le
  rintro x ⟨c, rfl⟩
  exact (Algebra.mem_bot).mpr (finite_algebra_hom_image_scalar f c)
end StrictEUnit
#print axioms StrictEUnit.finite_algebra_hom_range
#print axioms StrictEUnit.finite_algebra_hom_image_scalar
#print axioms StrictEUnit.finite_algebra_hom_range_eq_bot
