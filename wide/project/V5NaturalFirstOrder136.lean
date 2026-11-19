import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import TensorDerivation
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k L S N : Type*} [Field k] [CommRing L] [CommRing S] [CommRing N]
  [Algebra k L] [Algebra k S] [Algebra k N] [Algebra L S] [IsScalarTower k L S]
/-- Faithful-flat natural torsor invariants are exactly the structural scalar image.
No bialgebra, coassociativity or ambient domain hypothesis is used. -/
theorem v5_natural_fixed_image136 [Module.FaithfullyFlat L S]
    (ρ : S →ₐ[L] S ⊗[k] N) (e : S ⊗[L] S ≃ₐ[S] S ⊗[k] N)
    (he : ∀ a b, e (a ⊗ₜ[L] b) = a • ρ b)
    (y : S) (hy : ρ y = y ⊗ₜ[k] (1 : N)) :
    ∃ a : L, algebraMap L S a = y := by
  have hcan : (1 : S) ⊗ₜ[L] y = y ⊗ₜ[L] (1 : S) := by
    apply e.injective
    rw [he, one_smul, hy]
    exact (e.commutes y).symm
  let U := LinearMap.range (Algebra.linearMap L S)
  have hone : U.mkQ (1 : S) = 0 := by
    exact (Submodule.Quotient.mk_eq_zero U).mpr ⟨1, by simp⟩
  have hh := congrArg (U.mkQ.lTensor S) hcan
  have hq : U.mkQ y = 0 := by
    apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := L) (B := S) (S ⧸ U)
    change (1 : S) ⊗ₜ[L] U.mkQ y = (1 : S) ⊗ₜ[L] (0 : S ⧸ U)
    change (1 : S) ⊗ₜ[L] U.mkQ y = y ⊗ₜ[L] U.mkQ (1 : S) at hh
    rw [hone, TensorProduct.tmul_zero] at hh
    simpa only [TensorProduct.tmul_zero] using hh
  exact (Submodule.Quotient.mk_eq_zero U).mp hq

/-- A weighted unit for a differential natural torsor has a first-order
coefficient in the actual base. The coefficient is derived, not assumed. -/
theorem v5_natural_eigenunit_first_order136 [Module.FaithfullyFlat L S]
    (ρ : S →ₐ[L] S ⊗[k] N) (e : S ⊗[L] S ≃ₐ[S] S ⊗[k] N)
    (he : ∀ a b, e (a ⊗ₜ[L] b) = a • ρ b)
    (d : Derivation k S S)
    (hd : ∀ s, ρ (d s) = tensorDerivation d (ρ s))
    (χ : Nˣ) (v : Sˣ)
    (hv : ρ (v : S) = (v : S) ⊗ₜ[k] (χ : N)) :
    ∃ a : L, d (v : S) = algebraMap L S a * (v : S) := by
  have hdv : ρ (d (v : S)) = d (v : S) ⊗ₜ[k] (χ : N) := by
    rw [hd, hv, tensorDerivation_tmul]
  have hvi : ρ (↑v⁻¹ : S) = (↑v⁻¹ : S) ⊗ₜ[k] (↑χ⁻¹ : N) := by
    apply (v.isUnit.map ρ).mul_left_cancel
    rw [← map_mul, Units.mul_inv, map_one, hv, Algebra.TensorProduct.tmul_mul_tmul,
      Units.mul_inv, Units.mul_inv]
    rfl
  have hfix : ρ ((↑v⁻¹ : S) * d (v : S)) =
      ((↑v⁻¹ : S) * d (v : S)) ⊗ₜ[k] (1 : N) := by
    rw [map_mul, hvi, hdv, Algebra.TensorProduct.tmul_mul_tmul, Units.inv_mul]
  obtain ⟨a,ha⟩ := v5_natural_fixed_image136 ρ e he _ hfix
  refine ⟨a, ?_⟩
  rw [ha, mul_right_comm, Units.inv_mul, one_mul]
end StrictEUnit
#print axioms StrictEUnit.v5_natural_fixed_image136
#print axioms StrictEUnit.v5_natural_eigenunit_first_order136
