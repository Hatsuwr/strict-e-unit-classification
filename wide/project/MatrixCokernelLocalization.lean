import MatrixMinorBaseChange
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.RingTheory.LocalProperties.Projective

/-! Concrete localization of a matrix cokernel. No localization-presentation
compatibility is assumed. -/
noncomputable section
namespace StrictEUnit
variable {B : Type*} [CommRing B]
variable (S : Type*) [CommRing S] [Algebra B S]
variable (p : Submonoid B) [IsLocalization p S]
variable {n m : Type*} [Fintype n] [Fintype m]

def matrixCoordinateLocalization : (n → B) →ₗ[B] (n → S) :=
  LinearMap.pi fun i => (Algebra.linearMap B S).comp (LinearMap.proj i)

@[simp] theorem matrixCoordinateLocalization_apply (x:n→B) (i:n) :
    matrixCoordinateLocalization S x i = algebraMap B S (x i) := rfl

@[instance] theorem matrixCoordinateLocalization_isLocalized :
    IsLocalizedModule p (matrixCoordinateLocalization (n := n) S) := by
  dsimp [matrixCoordinateLocalization]
  infer_instance

theorem matrixCokernel_localized_range (A : Matrix n m B) :
    (LinearMap.range A.mulVecLin).localized' S p (matrixCoordinateLocalization S) =
      LinearMap.range ((A.map (algebraMap B S)).mulVecLin) := by
  rw [Matrix.range_mulVecLin, Submodule.localized'_span, Matrix.range_mulVecLin]
  congr 1
  rw [← Set.range_comp]
  rfl

abbrev matrixLocalizedCokernel (A : Matrix n m B) :=
  (n → S) ⧸ (LinearMap.range A.mulVecLin).localized' S p (matrixCoordinateLocalization S)

def matrixCokernelLocalizationMap (A : Matrix n m B) :
    ((n → B) ⧸ LinearMap.range A.mulVecLin) →ₗ[B] matrixLocalizedCokernel S p A :=
  (LinearMap.range A.mulVecLin).toLocalizedQuotient' S p (matrixCoordinateLocalization S)

@[instance] theorem matrixCokernelLocalizationMap_isLocalized (A : Matrix n m B) :
    IsLocalizedModule p (matrixCokernelLocalizationMap S p A) := by
  dsimp [matrixCokernelLocalizationMap]
  infer_instance

def matrixLocalizedCokernelEquiv (A : Matrix n m B) :
    matrixLocalizedCokernel S p A ≃ₗ[S]
      ((n → S) ⧸ LinearMap.range (A.map (algebraMap B S)).mulVecLin) :=
  Submodule.quotEquivOfEq _ _ (matrixCokernel_localized_range S p A)

theorem matrixLocalizedCokernel_projective [IsLocalRing S]
    (A : Matrix n m B) (r:ℕ) (ht:matrixMinorIdeal r A=⊤)
    (hz:matrixMinorIdeal (r+1) A=⊥) :
    Module.Projective S (matrixLocalizedCokernel S p A) := by
  letI := matrixCokernel_projective_baseChange (algebraMap B S) r A ht hz
  exact Module.Projective.of_equiv (matrixLocalizedCokernelEquiv S p A).symm

#print axioms matrixLocalizedCokernel
#print axioms matrixCoordinateLocalization
#print axioms matrixCoordinateLocalization_apply
#print axioms matrixCoordinateLocalization_isLocalized
#print axioms matrixCokernel_localized_range
#print axioms matrixCokernelLocalizationMap
#print axioms matrixCokernelLocalizationMap_isLocalized
#print axioms matrixLocalizedCokernelEquiv
#print axioms matrixLocalizedCokernel_projective
end StrictEUnit
