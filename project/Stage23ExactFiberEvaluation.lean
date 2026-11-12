import AlgebraicFiberQuotient
import FiberUnitComparison

/-! An exact kernel gives an injective algebra evaluation of the actual tensor fiber. -/
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
variable {k B R K : Type*} [Field k] [CommRing B] [CommRing R] [CommRing K]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
  [Algebra B k] [IsScalarTower k B k] [Algebra k K]

/-- The quotient evaluation afforded by equality of the full relation kernel
with the ideal extended from the base point. -/
def exactKernelQuotientEvaluation (ν : R →ₐ[k] K)
    (hker : RingHom.ker ν.toRingHom =
      Ideal.map (algebraMap B R) (RingHom.ker (algebraMap B k))) :
    (R ⧸ Ideal.map (algebraMap B R) (RingHom.ker (algebraMap B k))) →+* K :=
  Ideal.Quotient.lift _ ν.toRingHom (fun r hr =>
    show r ∈ RingHom.ker ν.toRingHom from hker.symm ▸ hr)

omit [Algebra k B] [IsScalarTower k B R] [IsScalarTower k B k] in
theorem exactKernelQuotientEvaluation_injective (ν : R →ₐ[k] K)
    (hker : RingHom.ker ν.toRingHom =
      Ideal.map (algebraMap B R) (RingHom.ker (algebraMap B k))) :
    Function.Injective (exactKernelQuotientEvaluation ν hker) :=
  RingHom.lift_injective_of_ker_le_ideal _ _ (le_of_eq hker)

/-- The actual tensor-fiber ring evaluation obtained from the proved quotient description. -/
def exactKernelFiberRingEvaluation (ν : R →ₐ[k] K)
    (hker : RingHom.ker ν.toRingHom =
      Ideal.map (algebraMap B R) (RingHom.ker (algebraMap B k))) :
    (k ⊗[B] R) →+* K :=
  algebraicFiberEvaluationFromQuotient (exactKernelQuotientEvaluation ν hker)

@[simp] theorem exactKernelFiberRingEvaluation_specialization (ν : R →ₐ[k] K)
    (hker : RingHom.ker ν.toRingHom =
      Ideal.map (algebraMap B R) (RingHom.ker (algebraMap B k))) (r : R) :
    exactKernelFiberRingEvaluation ν hker
      (algebraicFiberSpecialization (k := k) (B := B) r) = ν r := by
  change exactKernelQuotientEvaluation ν hker
    ((algebraicFiberQuotientEquiv (k := k) (B := B) (R := R)).symm (1 ⊗ₜ[B] r)) = ν r
  rw [← algebraicFiberQuotientEquiv_mk, RingEquiv.symm_apply_apply]
  rfl

/-- The whole-fiber map is a genuine k-algebra homomorphism, not just a ring map. -/
def exactKernelFiberEvaluation (ν : R →ₐ[k] K)
    (hker : RingHom.ker ν.toRingHom =
      Ideal.map (algebraMap B R) (RingHom.ker (algebraMap B k))) :
    (k ⊗[B] R) →ₐ[k] K :=
  { exactKernelFiberRingEvaluation ν hker with
    commutes' := fun a => by
      change exactKernelFiberRingEvaluation ν hker (algebraMap k (k ⊗[B] R) a) =
        algebraMap k K a
      rw [← (algebraicFiberSpecialization (k := k) (B := B) (R := R)).commutes a,
        exactKernelFiberRingEvaluation_specialization, ν.commutes] }

theorem exactKernelFiberEvaluation_injective (ν : R →ₐ[k] K)
    (hker : RingHom.ker ν.toRingHom =
      Ideal.map (algebraMap B R) (RingHom.ker (algebraMap B k))) :
    Function.Injective (exactKernelFiberEvaluation ν hker) :=
  algebraicFiberEvaluationFromQuotient_injective _
    (exactKernelQuotientEvaluation_injective ν hker)

@[simp] theorem exactKernelFiberEvaluation_specialization (ν : R →ₐ[k] K)
    (hker : RingHom.ker ν.toRingHom =
      Ideal.map (algebraMap B R) (RingHom.ker (algebraMap B k))) (r : R) :
    exactKernelFiberEvaluation ν hker
      (algebraicFiberSpecialization (k := k) (B := B) r) = ν r :=
  exactKernelFiberRingEvaluation_specialization ν hker r

end StrictEUnit
