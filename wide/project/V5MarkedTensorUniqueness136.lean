import V5MixedMarkedTensor135
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
variable {k B R S C : Type*}
  [CommRing k] [CommRing B] [CommRing R] [CommRing S] [CommRing C]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
  [Algebra k S] [Algebra B S] [Algebra k C]
/-- A tensor mark with the stated pure-tensor formula already proves that
its two factor marks agree on the tensor base. -/
theorem v5MarkedTensorBaseCompatibility136
    (pR : R →ₐ[k] k) (pS : S →ₐ[k] C) (pM : R ⊗[B] S →ₐ[k] C)
    (ht : ∀ r s, pM (r ⊗ₜ[B] s) = algebraMap k C (pR r) * pS s)
    (b : B) :
    algebraMap k C (pR (algebraMap B R b)) = pS (algebraMap B S b) := by
  have hb : (algebraMap B R b) ⊗ₜ[B] (1 : S) =
      (1 : R) ⊗ₜ[B] algebraMap B S b := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul]
  have h := congrArg pM hb
  simpa only [ht, map_one, mul_one, one_mul] using h
/-- The factor-mark formula uniquely identifies the existing tensor mark
with the generic marked tensor-point construction. -/
theorem v5MarkedTensorEq135136
    (pR : R →ₐ[k] k) (pS : S →ₐ[k] C) (pM : R ⊗[B] S →ₐ[k] C)
    (ht : ∀ r s, pM (r ⊗ₜ[B] s) = algebraMap k C (pR r) * pS s) :
    pM = v5MixedMarkedTensor135 pR pS
      (v5MarkedTensorBaseCompatibility136 pR pS pM ht) := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r s => rw [ht, v5MixedMarkedTensor135_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]
end StrictEUnit
#print axioms StrictEUnit.v5MarkedTensorBaseCompatibility136
#print axioms StrictEUnit.v5MarkedTensorEq135136
