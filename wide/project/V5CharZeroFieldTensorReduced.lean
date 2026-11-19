import V5PureTranscendentalTensorDomain
import V5AlgebraicTensorFiniteSupport
import V5SeparableTensorReduced
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.Algebra.CharP.Algebra

noncomputable section
open scoped TensorProduct
namespace StrictEUnit
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 50000
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule

/-- Arbitrary fields over a characteristic-zero base have reduced tensor
product. A transcendence basis is chosen, the pure-transcendental tensor is
proved a domain, and algebraic tensors are reduced by finite support and
separability. No finiteness or reduced-tensor hypothesis is assumed. -/
theorem v5_charZero_field_tensor_reduced
    (K E₁ E₂ : Type*) [Field K] [CharZero K] [Field E₁] [Field E₂]
    [Algebra K E₁] [Algebra K E₂] : IsReduced (E₁ ⊗[K] E₂) := by
  classical
  obtain ⟨σ, x, hx⟩ := exists_isTranscendenceBasis' K E₁
  let F := IntermediateField.adjoin K (Set.range x)
  letI : Algebra.IsAlgebraic F E₁ := hx.isAlgebraic_field
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  letI : IsDomain ((FractionRing (MvPolynomial σ K)) ⊗[K] E₂) :=
    v5_pureTranscendental_tensor_isDomain (K := K) (E := E₂) σ
  let eF := Algebra.TensorProduct.congr hx.1.aevalEquivField (AlgEquiv.refl (R := K) (A₁ := E₂))
  letI : IsDomain (F ⊗[K] E₂) := eF.symm.toMulEquiv.isDomain
  let D := F ⊗[K] E₂
  letI : IsReduced (E₁ ⊗[F] D) := by
    apply v5_reducedTensor_of_finiteSubfields
    intro U hU
    letI := hU
    letI : IsReduced (D ⊗[F] U) := v5_separable_tensor_domain_reduced F U D
    let c := Algebra.TensorProduct.comm F U D
    exact isReduced_of_injective c.toRingHom c.injective
  let e := Algebra.TensorProduct.cancelBaseChange K F F E₁ E₂
  exact isReduced_of_injective e.symm.toRingHom e.symm.injective

end StrictEUnit
#print axioms StrictEUnit.v5_charZero_field_tensor_reduced
