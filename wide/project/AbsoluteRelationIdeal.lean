import FiniteTypeGeometricDomain
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient

/-! Absolute primality of the actual finite-variable relation kernel follows
from relative closure; no scalar-extension primality is assumed. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped TensorProduct
namespace StrictEUnit

theorem finite_relation_ideal_map_isPrime
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [PerfectField F] [IsIntegrallyClosedIn F E]
    {σ : Type*} [Finite σ] (y : σ → E)
    (L : Type*) [Field L] [Algebra F L] :
    ((RingHom.ker (MvPolynomial.eval₂Hom (algebraMap F E) y)).map
      (MvPolynomial.map (algebraMap F L))).IsPrime := by
  classical
  let R := MvPolynomial σ F
  let f : R →ₐ[F] E := MvPolynomial.aeval y
  let I : Ideal R := RingHom.ker f
  let C := R ⧸ I
  change (I.map (MvPolynomial.map (algebraMap F L))).IsPrime
  letI : Algebra.FiniteType F R := Algebra.FiniteType.mvPolynomial F σ
  letI : Algebra.FiniteType F C := inferInstance
  let ι : C →ₐ[F] E := Ideal.kerLiftAlg f
  have hι : Function.Injective ι := Ideal.kerLiftAlg_injective f
  letI : IsDomain (L ⊗[F] C) :=
    finiteType_tensor_isDomain_of_relative_closed C ι hι L
  letI : IsDomain (C ⊗[F] L) :=
    (Algebra.TensorProduct.comm F C L).toMulEquiv.isDomain
  let S := R ⊗[F] L
  letI : IsDomain (C ⊗[R] S) :=
    (Algebra.TensorProduct.cancelBaseChange F R R C L).toMulEquiv.isDomain
  letI : IsDomain (S ⊗[R] C) :=
    (Algebra.TensorProduct.comm R S C).toMulEquiv.isDomain
  letI : IsDomain (S ⧸ I.map (algebraMap R S)) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).toMulEquiv.isDomain
  letI : (I.map (algebraMap R S)).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
  let e : S ≃ₐ[F] MvPolynomial σ L :=
    (Algebra.TensorProduct.comm F R L).trans
      ((MvPolynomial.algebraTensorAlgEquiv F L).restrictScalars F)
  have hcomp : e.toRingHom.comp (algebraMap R S) =
      MvPolynomial.map (algebraMap F L) := by
    apply RingHom.ext
    intro p
    change MvPolynomial.algebraTensorAlgEquiv F L (1 ⊗ₜ[F] p) = _
    simp only [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
    rfl
  have hp : ((I.map (algebraMap R S)).map e.toRingHom).IsPrime :=
    Ideal.map_isPrime_of_equiv e
  rw [Ideal.map_map, hcomp] at hp
  exact hp

end StrictEUnit
