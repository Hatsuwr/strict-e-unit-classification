import Mathlib.RingTheory.TensorProduct.Basic
noncomputable section
namespace StrictEUnit
variable {K X Y L F C : Type*} [Field K] [CommRing X] [CommRing Y]
  [CommRing F] [CommRing C]
/-- A formal first-order unit equation and exact tensor-mark comparison
suffice to transfer a constructed analytic exponential endpoint to the
original marked value. Both reciprocal marks may be retained in the input. -/
theorem v5MarkedExponentialEndpoint136
    (j : X →+* Y) (p : X →+* C) (Δ : Y →+ Y) (coeff : L → Y)
    (ev : F →+* C) (embed : K →+* C) (exp : K → C)
    (P : (Y →+* F) → Prop)
    (hrealization : ∃ η : Y →+* F, P η ∧
      ∀ u : Y, IsUnit u → ∀ l : L, Δ u = coeff l * u →
        ∃ α β : K, α ≠ 0 ∧ ev (η u) = embed α * exp β)
    (hmark : ∀ η : Y →+* F, P η → ∀ b : X, ev (η (j b)) = p b)
    (a c : C)
    (hlift : ∃ b : Xˣ, p (b : X) = a ∧ p (↑b⁻¹ : X) = c ∧
      ∃ l : L, Δ (j (b : X)) = coeff l * j (b : X)) :
    ∃ α β : K, α ≠ 0 ∧ a = embed α * exp β := by
  obtain ⟨b, hb, _, l, hDE⟩ := hlift
  obtain ⟨η, hη, hend⟩ := hrealization
  obtain ⟨α, β, hα, hv⟩ := hend (j (b : X)) (b.isUnit.map j) l hDE
  exact ⟨α, β, hα, ((hmark η hη (b : X)).trans hb).symm.trans hv⟩
end StrictEUnit
#print axioms StrictEUnit.v5MarkedExponentialEndpoint136
