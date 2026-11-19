import V5LaurentMark135
import V5MarkedKummerFactor
noncomputable section
namespace StrictEUnit
variable {k T C : Type*} [Field k] [CommRing T] [Algebra k T]
  [Algebra (LaurentPolynomial k) T] [CommRing C]
theorem v5AlgebraicMarkedKummer135 (f : k →+* C) (hf : Function.Injective f)
    (p : T → k)
    (hK : ∃ (q : ℕ) (_ : 0 < q) (α : T →ₐ[k] LaurentPolynomial k),
      α.toRingHom.comp (algebraMap (LaurentPolynomial k) T) = v5LaurentPower q ∧
      ∀ t, LaurentPolynomial.eval₂ f 1 (α t) = f (p t)) :
    ∃ (q : ℕ) (_ : 0 < q) (α : T →ₐ[k] LaurentPolynomial k),
      α.toRingHom.comp (algebraMap (LaurentPolynomial k) T) = v5LaurentPower q ∧
      ∀ t, v5LaurentMark135 k (α t) = p t := by
  obtain ⟨q,hq,α,hbase,hm⟩ := hK
  refine ⟨q,hq,α,hbase,fun t => hf ?_⟩
  rw [v5LaurentMark_map135]
  exact hm t
end StrictEUnit
#print axioms StrictEUnit.v5AlgebraicMarkedKummer135
