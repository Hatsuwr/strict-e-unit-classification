import V5TensorMarkedReverseEndpoint136
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k B L W C : Type*} [Field k]
  [CommRing B] [CommRing L] [CommRing W] [CommRing C]
  [Algebra k B] [Algebra k L] [Algebra B L] [IsScalarTower k B L]
  [Algebra k W] [Algebra B W] [Algebra k C]
/-- An explicit tensor rule can identify the coefficient operator after the
marked formal lift has already supplied that operator implicitly. -/
theorem v5TensorMarkedOperatorEndpoint136
    (pL : L →ₐ[k] k) (pW : W →ₐ[k] C)
    (hB : ∀ b, algebraMap k C (pL (algebraMap B L b)) = pW (algebraMap B W b))
    (E : L ⊗[B] W →+ L ⊗[B] W)
    {Q : C → C → Prop} {Rule : (L ⊗[B] W →+ L ⊗[B] W) → Prop}
    (hend : ∀ a c : C,
      (∃ b : (L ⊗[B] W)ˣ,
        v5MixedMarkedTensor135 pL pW hB (b : L ⊗[B] W) = a ∧
        v5MixedMarkedTensor135 pL pW hB (↑b⁻¹ : L ⊗[B] W) = c ∧
        ∃ l : L, E (b : L ⊗[B] W) = (l ⊗ₜ[B] (1 : W)) * (b : L ⊗[B] W)) → Q a c)
    (hEq : ∀ D : L ⊗[B] W →+ L ⊗[B] W, Rule D → ∀ x, D x = E x) :
    ∀ {D : L ⊗[B] W →+ L ⊗[B] W} (a c : C),
      (∃ b : (L ⊗[B] W)ˣ,
        v5MixedMarkedTensor135 pL pW hB (b : L ⊗[B] W) = a ∧
        v5MixedMarkedTensor135 pL pW hB (↑b⁻¹ : L ⊗[B] W) = c ∧
        ∃ l : L, D (b : L ⊗[B] W) = (l ⊗ₜ[B] (1 : W)) * (b : L ⊗[B] W)) →
      Rule D → Q a c := by
  intro D a c hlift hD
  obtain ⟨b, hba, hbc, l, hb⟩ := hlift
  exact hend a c ⟨b, hba, hbc, l, (hEq D hD _).symm.trans hb⟩
end StrictEUnit
#print axioms StrictEUnit.v5TensorMarkedOperatorEndpoint136
