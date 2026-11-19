import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

noncomputable section
open scoped TensorProduct
open TensorProduct
namespace StrictEUnit
variable {B R M : Type*} [CommRing B] [CommRing R] [Algebra B R]
  [AddCommGroup M] [Module B M]

/-- Finitely many generators after scalar extension come from one finitely
generated submodule before extension. No flatness is needed for this step. -/
theorem v5_finite_tensor_has_finite_source
    [Module.Finite R (R ⊗[B] M)] :
    ∃ N : Submodule B M, Module.Finite B N ∧
      Function.Surjective (N.subtype.lTensor R) := by
  obtain ⟨s, hsfin, hs⟩ := (Submodule.fg_def.mp
    (Module.Finite.fg_top (R := R) (M := R ⊗[B] M)))
  obtain ⟨N, hN, hNs⟩ := TensorProduct.exists_finite_submodule_right_of_finite s hsfin
  refine ⟨N, hN, ?_⟩
  let f : R ⊗[B] N →ₗ[R] R ⊗[B] M := AlgebraTensorModule.lTensor R R N.subtype
  have hf : Submodule.span R s ≤ LinearMap.range f := by
    apply Submodule.span_le.mpr
    exact hNs
  rw [hs] at hf
  have htop : LinearMap.range f = ⊤ := top_le_iff.mp hf
  have hfsurj : Function.Surjective f := LinearMap.range_eq_top.mp htop
  exact hfsurj

/-- Finite generation descends along a faithfully flat algebra. Supports of
the extended generators are constructed, and surjectivity of their finite
source is reflected by faithful flatness. -/
theorem v5_moduleFinite_of_faithfullyFlat_tensor
    [Module.FaithfullyFlat B R] [Module.Finite R (R ⊗[B] M)] :
    Module.Finite B M := by
  obtain ⟨N, hN, hsurj⟩ := v5_finite_tensor_has_finite_source (B := B) (R := R) (M := M)
  letI : Module.Finite B N := hN
  have hNsurj : Function.Surjective N.subtype :=
    (Module.FaithfullyFlat.lTensor_surjective_iff_surjective B R N.subtype).mp hsurj
  exact Module.Finite.of_surjective N.subtype hNsurj

/-- Convenient split-cover interface: a finite product model after faithful
flat extension proves finite generation of the original module. -/
theorem v5_moduleFinite_of_faithfullyFlat_split
    [Module.FaithfullyFlat B R] {J : Type*} [Finite J]
    (e : R ⊗[B] M ≃ₗ[R] (J → R)) : Module.Finite B M := by
  letI : Module.Finite R (R ⊗[B] M) := Module.Finite.equiv e.symm
  exact v5_moduleFinite_of_faithfullyFlat_tensor (R := R)

end StrictEUnit
#print axioms StrictEUnit.v5_finite_tensor_has_finite_source
#print axioms StrictEUnit.v5_moduleFinite_of_faithfullyFlat_tensor

#print axioms StrictEUnit.v5_moduleFinite_of_faithfullyFlat_split
