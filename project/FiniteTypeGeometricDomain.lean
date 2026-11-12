import AlgebraicBaseChangeDomain
import AlgebraicTensorDomain
import Mathlib.RingTheory.FiniteStability

/-! Arbitrary field base change of a finite-type algebra embedded in a relatively
closed extension. All domain instances are derived, not supplied as premises. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped TensorProduct
namespace StrictEUnit

theorem tensor_isDomain_of_injective_maps
    {F A B C D : Type*} [Field F] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra F A] [Algebra F B] [Algebra F C] [Algebra F D]
    [IsDomain (C ⊗[F] D)]
    (f : A →ₐ[F] C) (g : B →ₐ[F] D)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    IsDomain (A ⊗[F] B) := by
  let h : A ⊗[F] B →ₐ[F] C ⊗[F] D := Algebra.TensorProduct.map f g
  have hh : Function.Injective h :=
    TensorProduct.map_injective_of_flat_flat f.toLinearMap g.toLinearMap hf hg
  exact Function.Injective.isDomain h.toRingHom hh

theorem finiteType_tensor_isDomain_of_relative_closed
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [PerfectField F] [IsIntegrallyClosedIn F E]
    (C : Type*) [CommRing C] [Algebra F C] [Algebra.FiniteType F C]
    (ι : C →ₐ[F] E) (hι : Function.Injective ι)
    (L : Type*) [Field L] [Algebra F L] : IsDomain (L ⊗[F] C) := by
  let K := AlgebraicClosure F
  let M := AlgebraicClosure L
  letI : IsDomain (E ⊗[F] K) := relative_closed_tensor_isDomain_algebraic (E := E) K
  letI : IsDomain (K ⊗[F] E) := (Algebra.TensorProduct.comm F K E).toMulEquiv.isDomain
  letI : IsDomain (K ⊗[F] C) :=
    tensor_isDomain_of_injective_maps (AlgHom.id F K) ι Function.injective_id hι
  let j : K →ₐ[F] M := IsAlgClosed.lift
  letI : Algebra K M := j.toRingHom.toAlgebra
  letI : IsScalarTower F K M := IsScalarTower.of_algHom j
  letI : IsDomain (M ⊗[K] (K ⊗[F] C)) :=
    algebraic_tensor_isDomain (k := K) (A := M) (B := K ⊗[F] C)
  let e := Algebra.TensorProduct.cancelBaseChange F K K M C
  letI : IsDomain (M ⊗[F] C) := e.symm.toMulEquiv.isDomain
  exact tensor_isDomain_of_injective_maps
    (IsScalarTower.toAlgHom F L M) (AlgHom.id F C)
    (algebraMap L M).injective Function.injective_id

end StrictEUnit
