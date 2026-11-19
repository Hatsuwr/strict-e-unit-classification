import TensorUnitFactorization
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Associator

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
open scoped TensorProduct
open TensorProduct
namespace StrictEUnit
variable {k C H : Type*} [Field k] [CommRing C] [CommRing H]
  [Algebra k C] [Algebra k H]

/-- A nonzero vector admits a normalized scalar-linear retraction; no algebra
point of its containing ring is used. -/
theorem v5_scalar_retraction {V : Type*} [AddCommGroup V] [Module k V]
    (x : V) (hx : x ≠ 0) : ∃ f : V →ₗ[k] k, f x = 1 := by
  obtain ⟨f, hf⟩ := (LinearMap.toSpanSingleton k V x).exists_leftInverse_of_injective
    (LinearMap.ker_toSpanSingleton k V hx)
  refine ⟨f, ?_⟩
  have h := congrArg (fun g : k →ₗ[k] k => g 1) hf
  simpa only [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply,
    one_smul, LinearMap.id_apply] using h

theorem v5_tmul_left_injective {V W : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (x : V) (hx : x ≠ 0) :
    Function.Injective (fun y : W => x ⊗ₜ[k] y) := by
  obtain ⟨f, hf⟩ := v5_scalar_retraction (k := k) x hx
  intro y z hyz
  have h := congrArg (fun t => TensorProduct.lid k W ((f.rTensor W) t)) hyz
  simpa only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, hf, one_smul] using h

/-- Every unit of a domain coaction has a pure weight. The tensor-unit theorem
supplies purity; counit normalization puts the original unit in the first slot. -/
theorem v5_domainCoaction_unit_weight [IsAlgClosed k] [IsDomain C] [IsDomain H]
    (δ : C →ₐ[k] C ⊗[k] H) (ε : H →ₐ[k] k)
    (hcounit : ∀ c, (TensorProduct.rid k C)
      ((LinearMap.lTensor C ε.toLinearMap) (δ c)) = c)
    (u : Cˣ) : ∃ χ : H, δ (u : C) = (u : C) ⊗ₜ[k] χ := by
  obtain ⟨a, h, hh⟩ := tensor_unit_is_pure (Units.map δ.toMonoidHom u)
  change δ (u : C) = a ⊗ₜ[k] h at hh
  have hu : ε h • a = (u : C) := by
    have he := hcounit (u : C)
    rw [hh, LinearMap.lTensor_tmul, TensorProduct.rid_tmul] at he
    exact he
  have he : ε h ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at hu
    exact u.ne_zero hu.symm
  refine ⟨(ε h)⁻¹ • h, ?_⟩
  rw [hh, ← hu, TensorProduct.smul_tmul_smul,
    mul_inv_cancel₀ he, one_smul]

/-- Coassociativity and counit make the normalized weight of any unit an
invertible grouplike element. This does not construct an actual wide coaction. -/
theorem v5_domainCoaction_unit_character [IsAlgClosed k] [IsDomain C] [IsDomain H]
    (δ : C →ₐ[k] C ⊗[k] H) (ε : H →ₐ[k] k)
    (Δ : H →ₐ[k] H ⊗[k] H)
    (hcounit : ∀ c, (TensorProduct.rid k C)
      ((LinearMap.lTensor C ε.toLinearMap) (δ c)) = c)
    (hcoassoc : ∀ c,
      TensorProduct.assoc k C H H
        ((LinearMap.rTensor H δ.toLinearMap) (δ c)) =
      (LinearMap.lTensor C Δ.toLinearMap) (δ c))
    (u : Cˣ) :
    ∃ χ : Hˣ, δ (u : C) = (u : C) ⊗ₜ[k] (χ : H) ∧
      ε (χ : H) = 1 ∧ Δ (χ : H) = (χ : H) ⊗ₜ[k] (χ : H) := by
  obtain ⟨a, ha⟩ := v5_domainCoaction_unit_weight δ ε hcounit u
  obtain ⟨b, hb⟩ := v5_domainCoaction_unit_weight δ ε hcounit u⁻¹
  have hab : a * b = 1 := by
    apply v5_tmul_left_injective (k := k) (1 : C) one_ne_zero
    have he := congrArg δ u.val_inv
    change δ ((u : C) * (↑u⁻¹ : C)) = δ 1 at he
    rw [map_mul, ha, hb, Algebra.TensorProduct.tmul_mul_tmul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one] at he
    simpa only [Algebra.TensorProduct.one_def] using he
  let χ : Hˣ := ⟨a, b, hab, by simpa only [mul_comm] using hab⟩
  refine ⟨χ, ha, ?_, ?_⟩
  · have he := hcounit (u : C)
    rw [ha, LinearMap.lTensor_tmul, TensorProduct.rid_tmul] at he
    change ε a • (u : C) = (u : C) at he
    have hm : (ε a - 1) • (u : C) = 0 := by rw [sub_smul, one_smul, he, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hm).resolve_right u.ne_zero)
  · have he := hcoassoc (u : C)
    rw [ha, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul] at he
    change TensorProduct.assoc k C H H (δ (u : C) ⊗ₜ[k] a) = (u : C) ⊗ₜ[k] Δ a at he
    rw [ha, TensorProduct.assoc_tmul] at he
    exact (v5_tmul_left_injective (k := k) (u : C) u.ne_zero he).symm

end StrictEUnit
#print axioms StrictEUnit.v5_scalar_retraction
#print axioms StrictEUnit.v5_tmul_left_injective
#print axioms StrictEUnit.v5_domainCoaction_unit_weight
#print axioms StrictEUnit.v5_domainCoaction_unit_character
