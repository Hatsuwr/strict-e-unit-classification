import V5TensorMarkedExponentialEndpoint136
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k B L W C : Type*} [Field k]
  [CommRing B] [CommRing L] [CommRing W] [CommRing C]
  [Algebra k B] [Algebra k L] [Algebra B L] [IsScalarTower k B L]
  [Algebra k W] [Algebra B W] [Algebra k C]
/-- Transfer a formal first-order equation from coefficient-first tensor
orientation to solution-first orientation using the checked commutation law. -/
theorem v5TensorFirstOrderTranspose136
    (dX : L ⊗[B] W →+ L ⊗[B] W) (dY : W ⊗[B] L →+ W ⊗[B] L)
    (hcomm : ∀ y, dX (Algebra.TensorProduct.comm B W L y) =
      Algebra.TensorProduct.comm B W L (dY y))
    (x : L ⊗[B] W) (l : L)
    (hx : dX x = (l ⊗ₜ[B] (1 : W)) * x) :
    dY (Algebra.TensorProduct.comm B L W x) =
      ((1 : W) ⊗ₜ[B] l) * Algebra.TensorProduct.comm B L W x := by
  apply (Algebra.TensorProduct.comm B W L).injective
  have hback : ∀ z : L ⊗[B] W,
      Algebra.TensorProduct.comm B W L (Algebra.TensorProduct.comm B L W z) = z := by
    intro z
    exact (Algebra.TensorProduct.comm B L W).symm_apply_apply z
  rw [← hcomm, hback, map_mul, hback]
  exact hx
/-- Any endpoint for the commuted formal equation is an endpoint for the
coefficient-first formal equation, with the same unit and both marks. -/
theorem v5TensorMarkedReverseEndpoint136
    (pL : L →ₐ[k] k) (pW : W →ₐ[k] C)
    (hB : ∀ b, algebraMap k C (pL (algebraMap B L b)) = pW (algebraMap B W b))
    (dX : L ⊗[B] W →+ L ⊗[B] W) (dY : W ⊗[B] L →+ W ⊗[B] L)
    (hcomm : ∀ y, dX (Algebra.TensorProduct.comm B W L y) =
      Algebra.TensorProduct.comm B W L (dY y))
    {Q : C → C → Prop}
    (hend : ∀ a c : C,
      (∃ b : (L ⊗[B] W)ˣ,
        v5MixedMarkedTensor135 pL pW hB (b : L ⊗[B] W) = a ∧
        v5MixedMarkedTensor135 pL pW hB (↑b⁻¹ : L ⊗[B] W) = c ∧
        ∃ l : L, dY (Algebra.TensorProduct.comm B L W (b : L ⊗[B] W)) =
          ((1 : W) ⊗ₜ[B] l) * Algebra.TensorProduct.comm B L W (b : L ⊗[B] W)) → Q a c) :
    ∀ a c : C,
      (∃ b : (L ⊗[B] W)ˣ,
        v5MixedMarkedTensor135 pL pW hB (b : L ⊗[B] W) = a ∧
        v5MixedMarkedTensor135 pL pW hB (↑b⁻¹ : L ⊗[B] W) = c ∧
        ∃ l : L, dX (b : L ⊗[B] W) = (l ⊗ₜ[B] (1 : W)) * (b : L ⊗[B] W)) → Q a c := by
  intro a c hb
  obtain ⟨b, hba, hbc, l, hDE⟩ := hb
  exact hend a c ⟨b, hba, hbc, l, v5TensorFirstOrderTranspose136 dX dY hcomm _ l hDE⟩
end StrictEUnit
#print axioms StrictEUnit.v5TensorFirstOrderTranspose136
#print axioms StrictEUnit.v5TensorMarkedReverseEndpoint136
