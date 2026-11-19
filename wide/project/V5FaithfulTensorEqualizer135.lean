import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.TensorProduct.Basic
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
variable {L S W : Type*} [CommRing L] [CommRing S] [CommRing W]
  [Algebra L S] [Algebra L W] [Module.FaithfullyFlat L S]
/-- The faithfully flat tensor equalizer with arbitrary coefficient algebra.
No flatness hypothesis on W is required. -/
theorem v5_faithful_tensor_equalizer135
    (x : S ⊗[L] W)
    (hx : ((Algebra.TensorProduct.includeRight : S ⊗[L] W →ₐ[L]
      S ⊗[L] (S ⊗[L] W)) x) =
      Algebra.TensorProduct.map (AlgHom.id L S)
        (Algebra.TensorProduct.includeRight : W →ₐ[L] S ⊗[L] W) x) :
    ∃ w : W, (Algebra.TensorProduct.includeRight : W →ₐ[L] S ⊗[L] W) w = x := by
  let φ : W →ₐ[L] S ⊗[L] W := Algebra.TensorProduct.includeRight
  let U := LinearMap.range φ.toLinearMap
  have hφ (w : W) : U.mkQ (φ w) = 0 := by
    exact (Submodule.Quotient.mk_eq_zero U).mpr ⟨w, rfl⟩
  have hd (y : S ⊗[L] W) :
      U.mkQ.lTensor S (Algebra.TensorProduct.map (AlgHom.id L S) φ y) = 0 := by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => simp only [map_add, hy, hz, add_zero]
    | tmul s w =>
      change s ⊗ₜ[L] U.mkQ (φ w) = 0
      rw [hφ, TensorProduct.tmul_zero]
  have he := congrArg (U.mkQ.lTensor S) hx
  have hq : U.mkQ x = 0 := by
    apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := L) (B := S) (S ⊗[L] W ⧸ U)
    change (1 : S) ⊗ₜ[L] U.mkQ x = (1 : S) ⊗ₜ[L] (0 : (S ⊗[L] W) ⧸ U)
    rw [TensorProduct.tmul_zero]
    exact he.trans (hd x)
  exact (Submodule.Quotient.mk_eq_zero U).mp hq

theorem v5_faithful_includeRight_injective135 :
    Function.Injective (Algebra.TensorProduct.includeRight : W →ₐ[L] S ⊗[L] W) :=
  Module.FaithfullyFlat.tensorProduct_mk_injective (A := L) (B := S) W
end StrictEUnit
#print axioms StrictEUnit.v5_faithful_tensor_equalizer135
#print axioms StrictEUnit.v5_faithful_includeRight_injective135
