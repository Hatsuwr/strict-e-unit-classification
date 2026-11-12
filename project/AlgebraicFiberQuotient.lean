import AlgebraicFiberDomain
import Mathlib.RingTheory.TensorProduct.Quotient

/-! The actual tensor fiber is the quotient by the extended base-point kernel.
This does not assume a numerical identification or integrality. -/
open scoped TensorProduct
noncomputable section
namespace StrictEUnit
variable {k B R : Type*} [CommRing k] [CommRing B] [CommRing R]
  [Algebra k B] [Algebra B k] [IsScalarTower k B k] [Algebra B R]

/-- Every k-valued base point is surjective because it fixes k. -/
theorem basePoint_algebraMap_surjective : Function.Surjective (algebraMap B k) := by
  intro a
  refine ⟨algebraMap k B a, ?_⟩
  rw [← IsScalarTower.algebraMap_apply k B k]
  simp

/-- A genuine quotient description of the tensor fiber. -/
def algebraicFiberQuotientEquiv :
    (R ⧸ Ideal.map (algebraMap B R) (RingHom.ker (algebraMap B k))) ≃+* (k ⊗[B] R) :=
  let q : (B ⧸ RingHom.ker (algebraMap B k)) ≃ₐ[B] k :=
    Ideal.quotientKerAlgEquivOfSurjective
      (f := Algebra.ofId B k) (basePoint_algebraMap_surjective (k:=k) (B:=B))
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot R
    (RingHom.ker (algebraMap B k))).toRingEquiv.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl (R:=R) (A₁:=R)) q).toRingEquiv.trans
      (Algebra.TensorProduct.comm B R k).toRingEquiv)

@[simp] theorem algebraicFiberQuotientEquiv_mk (r : R) :
    algebraicFiberQuotientEquiv (k:=k) (B:=B) (R:=R)
      (Ideal.Quotient.mk _ r) = 1 ⊗ₜ[B] r := by
  simp [algebraicFiberQuotientEquiv]

/-- A quotient embedding induces an actual injective evaluation of the full tensor fiber. -/
def algebraicFiberEvaluationFromQuotient {L : Type*} [CommRing L]
    (ν : (R ⧸ Ideal.map (algebraMap B R) (RingHom.ker (algebraMap B k))) →+* L) :
    (k ⊗[B] R) →+* L :=
  ν.comp (algebraicFiberQuotientEquiv (k:=k) (B:=B) (R:=R)).symm.toRingHom

theorem algebraicFiberEvaluationFromQuotient_injective {L : Type*} [CommRing L]
    (ν : (R ⧸ Ideal.map (algebraMap B R) (RingHom.ker (algebraMap B k))) →+* L)
    (hν : Function.Injective ν) :
    Function.Injective (algebraicFiberEvaluationFromQuotient ν) :=
  hν.comp (algebraicFiberQuotientEquiv (k:=k) (B:=B) (R:=R)).symm.injective

/-- Domain transfer uses the proved quotient identification, not an
assumption that specialization preserves domains. -/
theorem algebraicFiber_isDomain_of_quotient
    [IsDomain (R ⧸ Ideal.map (algebraMap B R) (RingHom.ker (algebraMap B k)))] :
    IsDomain (k ⊗[B] R) :=
  Function.Injective.isDomain (algebraicFiberQuotientEquiv (k:=k) (B:=B) (R:=R)).symm.toRingHom
    (algebraicFiberQuotientEquiv (k:=k) (B:=B) (R:=R)).symm.injective
/-- Exact numerical relations prove integrality of the actual tensor fiber. -/
theorem algebraicFiber_isDomain_of_exact_evaluation {L : Type*} [CommRing L] [IsDomain L]
    (ev : R →+* L)
    (hker : RingHom.ker ev = Ideal.map (algebraMap B R) (RingHom.ker (algebraMap B k))) :
    IsDomain (k ⊗[B] R) := by
  let J := Ideal.map (algebraMap B R) (RingHom.ker (algebraMap B k))
  have hJ : ∀ r, r ∈ J → ev r = 0 := fun r hr =>
    show r ∈ RingHom.ker ev from hker.symm ▸ hr
  let ν := Ideal.Quotient.lift J ev hJ
  have hν : Function.Injective ν :=
    RingHom.lift_injective_of_ker_le_ideal J hJ (le_of_eq hker)
  letI : IsDomain (R ⧸ J) := Function.Injective.isDomain ν hν
  exact algebraicFiber_isDomain_of_quotient (k:=k) (B:=B) (R:=R)

end StrictEUnit
#print axioms StrictEUnit.basePoint_algebraMap_surjective
#print axioms StrictEUnit.algebraicFiberQuotientEquiv
#print axioms StrictEUnit.algebraicFiber_isDomain_of_quotient

#print axioms StrictEUnit.algebraicFiberQuotientEquiv_mk
#print axioms StrictEUnit.algebraicFiberEvaluationFromQuotient
#print axioms StrictEUnit.algebraicFiberEvaluationFromQuotient_injective

#print axioms StrictEUnit.algebraicFiber_isDomain_of_exact_evaluation
