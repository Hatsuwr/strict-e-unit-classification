import V5MarkedExponentialEndpoint136
import V5MixedMarkedTensor135
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k B L W F C : Type*} [Field k]
  [CommRing B] [CommRing L] [CommRing W] [CommRing F] [CommRing C]
  [Algebra k B] [Algebra k L] [Algebra B L] [IsScalarTower k B L]
  [Algebra k W] [Algebra B W] [Algebra k C]
/-- Assemble the commuted tensor map and marked tensor point before
specializing large actual coefficient rings. -/
theorem v5TensorMarkedExponentialEndpoint136
    (pL : L →ₐ[k] k) (pW : W →ₐ[k] C)
    (hB : ∀ b, algebraMap k C (pL (algebraMap B L b)) = pW (algebraMap B W b))
    (Δ : W ⊗[B] L →+ W ⊗[B] L)
    (ev : F →+* C) (embed : k →+* C) (exp : k → C)
    (P : (W ⊗[B] L →+* F) → Prop)
    (hrealization : ∃ η : W ⊗[B] L →+* F, P η ∧
      ∀ u : W ⊗[B] L, IsUnit u → ∀ l : L,
        Δ u = ((1 : W) ⊗ₜ[B] l) * u →
        ∃ α β : k, α ≠ 0 ∧ ev (η u) = embed α * exp β)
    (hmark : ∀ η : W ⊗[B] L →+* F, P η → ∀ b : L ⊗[B] W,
      ev (η (Algebra.TensorProduct.comm B L W b)) = v5MixedMarkedTensor135 pL pW hB b) :
    ∀ a c : C,
      (∃ b : (L ⊗[B] W)ˣ,
        v5MixedMarkedTensor135 pL pW hB (b : L ⊗[B] W) = a ∧
        v5MixedMarkedTensor135 pL pW hB (↑b⁻¹ : L ⊗[B] W) = c ∧
        ∃ l : L, Δ (Algebra.TensorProduct.comm B L W (b : L ⊗[B] W)) =
          ((1 : W) ⊗ₜ[B] l) * Algebra.TensorProduct.comm B L W (b : L ⊗[B] W)) →
      ∃ α β : k, α ≠ 0 ∧ a = embed α * exp β :=
  v5MarkedExponentialEndpoint136 (Algebra.TensorProduct.comm B L W).toRingHom
    (v5MixedMarkedTensor135 pL pW hB).toRingHom Δ (fun l => (1 : W) ⊗ₜ[B] l)
    ev embed exp P hrealization hmark
end StrictEUnit
#print axioms StrictEUnit.v5TensorMarkedExponentialEndpoint136
