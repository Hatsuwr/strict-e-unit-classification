import AlgebraicFiber

/-! Domain transfer along the constructed algebraic fiber chart. Injectivity
of a numerical evaluation, when used, is an explicit remaining hypothesis:
no claim that the functional ring being a domain makes its fiber a domain. -/
open scoped TensorProduct
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
variable {k B R H : Type*} [Field k] [CommRing B] [CommRing R] [CommRing H]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
  [Algebra B k] [IsScalarTower k B k] [Algebra k H]
  [IsAlgClosed k] [Algebra.FiniteType B R] [Module.FaithfullyFlat B R]

/-- Domain of the actual algebraic fiber suffices for domain of H. -/
theorem group_isDomain_of_algebraicFiber
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) [IsDomain (k ⊗[B] R)] : IsDomain H :=
  Function.Injective.isDomain (algebraicFiberTrivialization e).symm.toAlgHom
    (algebraicFiberTrivialization e).symm.injective

/-- Conversely, the genuine chart transfers domain of H to the whole fiber. -/
theorem algebraicFiber_isDomain_of_group
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) [IsDomain H] : IsDomain (k ⊗[B] R) :=
  Function.Injective.isDomain (algebraicFiberTrivialization e).toAlgHom
    (algebraicFiberTrivialization e).injective

variable {L : Type*} [CommRing L] [Algebra k L]

/-- The actual group evaluation induced by a fiber evaluation and its chart. -/
def algebraicFiberGroupEvaluation
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) (ν : (k ⊗[B] R) →ₐ[k] L) : H →ₐ[k] L :=
  ν.comp (algebraicFiberTrivialization e).symm.toAlgHom

@[simp] theorem algebraicFiberGroupEvaluation_chart
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) (ν : (k ⊗[B] R) →ₐ[k] L)
    (x : k ⊗[B] R) :
    algebraicFiberGroupEvaluation e ν (algebraicFiberTrivialization e x) = ν x := by
  simp [algebraicFiberGroupEvaluation]

theorem algebraicFiberGroupEvaluation_injective
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) (ν : (k ⊗[B] R) →ₐ[k] L)
    (hν : Function.Injective ν) : Function.Injective (algebraicFiberGroupEvaluation e ν) :=
  hν.comp (algebraicFiberTrivialization e).symm.injective

omit [Algebra k B] [Algebra k R] [IsScalarTower k B R] [IsScalarTower k B k]
  [IsAlgClosed k] [Algebra.FiniteType B R] [Module.FaithfullyFlat B R] in
/-- A verified injective evaluation into a domain proves fiber integrality. -/
theorem algebraicFiber_isDomain_of_injective_evaluation [IsDomain L]
    (ν : (k ⊗[B] R) →ₐ[k] L) (hν : Function.Injective ν) :
    IsDomain (k ⊗[B] R) := Function.Injective.isDomain ν hν

/-- The precise numerical-identification boundary: evaluation must be
injective on the entire algebraic fiber, not merely defined on it. -/
theorem group_isDomain_of_injective_fiber_evaluation [IsDomain L]
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) (ν : (k ⊗[B] R) →ₐ[k] L)
    (hν : Function.Injective ν) : IsDomain H :=
  Function.Injective.isDomain (algebraicFiberGroupEvaluation e ν)
    (algebraicFiberGroupEvaluation_injective e ν hν)
end StrictEUnit
#print axioms StrictEUnit.group_isDomain_of_algebraicFiber
#print axioms StrictEUnit.algebraicFiber_isDomain_of_group
#print axioms StrictEUnit.algebraicFiberGroupEvaluation
#print axioms StrictEUnit.algebraicFiberGroupEvaluation_chart
#print axioms StrictEUnit.algebraicFiberGroupEvaluation_injective
#print axioms StrictEUnit.algebraicFiber_isDomain_of_injective_evaluation
#print axioms StrictEUnit.group_isDomain_of_injective_fiber_evaluation
