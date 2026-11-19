import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Unramified.Pi
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.StdBasis

noncomputable section
open scoped TensorProduct
namespace StrictEUnit
universe u v w
set_option maxHeartbeats 400000
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {B : Type v} {R : Type u} {C : Type w} [CommRing B] [CommRing R] [CommRing C]
    [Algebra B R] [Algebra B C] [Module.FaithfullyFlat B R]

/-- Vanishing of relative differentials descends through faithfully flat
base change. No finite-generation or split-product hypothesis is needed. -/
theorem v5_formallyUnramified_of_faithfullyFlat_baseChange
    [Algebra.FormallyUnramified R (R ⊗[B] C)] : Algebra.FormallyUnramified B C := by
  letI : Algebra C (R ⊗[B] C) := Algebra.TensorProduct.rightAlgebra
  letI : IsScalarTower B C (R ⊗[B] C) := Algebra.TensorProduct.right_isScalarTower
  let e := KaehlerDifferential.tensorKaehlerEquiv B R C (R ⊗[B] C)
  letI : Subsingleton (R ⊗[B] Ω[C⁄B]) := e.injective.subsingleton
  exact ⟨Module.FaithfullyFlat.lTensor_reflects_triviality B R (Ω[C⁄B])⟩

/-- A finite split base change is flat over R, hence C is flat over B. -/
theorem v5_split_baseChange_flat {ι : Type u} [Finite ι]
    (e : R ⊗[B] C ≃ₐ[R] (ι → R)) : Module.Flat B C := by
  letI : Module.Flat R (R ⊗[B] C) := Module.Flat.of_linearEquiv e.toLinearEquiv
  exact Module.Flat.of_flat_tensorProduct B C R

/-- A finite split base change has no relative differentials, and therefore
the original algebra is formally unramified. This is not an etale claim. -/
theorem v5_split_baseChange_formallyUnramified {ι : Type u} [Finite ι]
    (e : R ⊗[B] C ≃ₐ[R] (ι → R)) : Algebra.FormallyUnramified B C := by
  letI : Algebra.FormallyUnramified R (R ⊗[B] C) :=
    Algebra.FormallyUnramified.of_equiv e.symm
  exact v5_formallyUnramified_of_faithfullyFlat_baseChange (R := R)

/-- The original Kaehler module vanishes, with no extra kernel assumption. -/
theorem v5_split_baseChange_kaehler_zero {ι : Type u} [Finite ι]
    (e : R ⊗[B] C ≃ₐ[R] (ι → R)) : Subsingleton (Ω[C⁄B]) := by
  letI := v5_split_baseChange_formallyUnramified e
  infer_instance

/-- With module finiteness supplied separately, the split descent is a
finite unramified flat algebra. Formal smoothness/etaleness is not asserted. -/
theorem v5_split_baseChange_unramified [Module.Finite B C] {ι : Type u} [Finite ι]
    (e : R ⊗[B] C ≃ₐ[R] (ι → R)) : Algebra.Unramified B C where
  formallyUnramified := v5_split_baseChange_formallyUnramified e

end StrictEUnit
#print axioms StrictEUnit.v5_formallyUnramified_of_faithfullyFlat_baseChange
#print axioms StrictEUnit.v5_split_baseChange_flat
#print axioms StrictEUnit.v5_split_baseChange_formallyUnramified
#print axioms StrictEUnit.v5_split_baseChange_kaehler_zero
#print axioms StrictEUnit.v5_split_baseChange_unramified
