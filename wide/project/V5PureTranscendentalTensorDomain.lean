import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.Algebra.Equiv.TransferInstance

open scoped TensorProduct nonZeroDivisors
noncomputable section
namespace StrictEUnit
set_option maxHeartbeats 400000
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule

/-- Localizing the first factor preserves a domain tensor product over a field. -/
theorem v5_fraction_tensor_isDomain_of_polynomialTensor
    {K P E : Type*} [Field K] [CommRing P] [IsDomain P] [Field E]
    [Algebra K P] [Algebra K E] [IsDomain (P ⊗[K] E)] :
    IsDomain ((FractionRing P) ⊗[K] E) := by
  let F := FractionRing P
  let T := P ⊗[K] E
  let U := F ⊗[P] T
  letI : Algebra T U := Algebra.TensorProduct.rightAlgebra
  letI : IsScalarTower P T U := Algebra.TensorProduct.right_isScalarTower
  have hl : IsLocalization (Algebra.algebraMapSubmonoid T P⁰) U := by
    apply isLocalizedModule_iff_isLocalization.mp
    change IsLocalizedModule P⁰ (TensorProduct.mk P F T 1)
    infer_instance
  letI := hl
  have hinj : Function.Injective (algebraMap P T) :=
    Algebra.TensorProduct.includeLeft_injective (R := K) (S := P) (A := P) (B := E) (RingHom.injective (algebraMap K E))
  have hden : Algebra.algebraMapSubmonoid T P⁰ ≤ T⁰ :=
    map_le_nonZeroDivisors_of_injective (algebraMap P T) hinj le_rfl
  letI : IsDomain U := IsLocalization.isDomain_of_le_nonZeroDivisors T hden
  let e := Algebra.TensorProduct.cancelBaseChange K P F F E
  exact e.symm.toMulEquiv.isDomain

/-- A purely transcendental fraction field remains a domain after arbitrary
field base extension. The variable type may be infinite. -/
theorem v5_pureTranscendental_tensor_isDomain
    {K E : Type*} [Field K] [Field E] [Algebra K E] (σ : Type*) :
    IsDomain ((FractionRing (MvPolynomial σ K)) ⊗[K] E) := by
  classical
  letI : IsDomain ((MvPolynomial σ K) ⊗[K] E) :=
    (MvPolynomial.scalarRTensorAlgEquiv (σ := σ) (R := K) (N := E)).toMulEquiv.isDomain
  exact v5_fraction_tensor_isDomain_of_polynomialTensor

/-- The symmetric tensor order of the same actual field base change. -/
theorem v5_pureTranscendental_tensor_left_isDomain
    {K E : Type*} [Field K] [Field E] [Algebra K E] (σ : Type*) :
    IsDomain (E ⊗[K] (FractionRing (MvPolynomial σ K))) := by
  letI := v5_pureTranscendental_tensor_isDomain (K := K) (E := E) σ
  exact (Algebra.TensorProduct.comm K E (FractionRing (MvPolynomial σ K))).toMulEquiv.isDomain

end StrictEUnit
#print axioms StrictEUnit.v5_fraction_tensor_isDomain_of_polynomialTensor
#print axioms StrictEUnit.v5_pureTranscendental_tensor_isDomain

#print axioms StrictEUnit.v5_pureTranscendental_tensor_left_isDomain
