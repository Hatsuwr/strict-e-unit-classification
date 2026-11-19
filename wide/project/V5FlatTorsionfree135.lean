import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
/-- Flat modules over a domain are torsion-free, proved directly by tensoring multiplication. -/
theorem v5_noZeroSMulDivisors_of_flat135
    {B M : Type*} [CommRing B] [IsDomain B] [AddCommGroup M] [Module B M]
    [Module.Flat B M] : NoZeroSMulDivisors B M := by
  refine ⟨?_⟩
  intro b m hbm
  by_cases hb : b = 0
  · exact Or.inl hb
  · right
    have hf : Function.Injective (LinearMap.mulLeft B b) := by
      intro x y h
      exact mul_left_cancel₀ hb h
    have ht := Module.Flat.lTensor_preserves_injective_linearMap
      (M := M) (LinearMap.mulLeft B b) hf
    have hz : (LinearMap.mulLeft B b).lTensor M (m ⊗ₜ[B] (1 : B)) =
        (LinearMap.mulLeft B b).lTensor M (0 : M ⊗[B] B) := by
      change m ⊗ₜ[B] (b * 1) = 0
      rw [mul_one]
      calc
        m ⊗ₜ[B] b = m ⊗ₜ[B] (b • (1 : B)) := by rw [smul_eq_mul, mul_one]
        _ = (b • m) ⊗ₜ[B] (1 : B) := (TensorProduct.smul_tmul b m (1 : B)).symm
        _ = 0 := by rw [hbm, TensorProduct.zero_tmul]
    have h := congrArg (TensorProduct.rid B M) (ht hz)
    simpa using h
end StrictEUnit
#print axioms StrictEUnit.v5_noZeroSMulDivisors_of_flat135
