import V5ComponentNaturality132
import V5ProductComponentInvariants
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
variable {k H N J : Type*} [Field k] [CommRing H] [CommRing N]
  [Algebra k H] [Algebra k N] [Finite J]

/-- Coordinate normalization of the existing canonical invariant equivalence.
It is proved from regular-action invariance, not assumed separately. -/
theorem v5ProductComponentFixedEquiv_coordinates132
    (C : H ≃ₐ[k] (J → N))
    (ρ : H →ₐ[k] H ⊗[k] N) (Δ : N →ₐ[k] N ⊗[k] N) (ε : N →ₐ[k] k)
    (hleft : ∀ n, v5ComponentLeftScalar ε (Δ n) = n)
    (he : ∀ x i, Algebra.TensorProduct.map (v5ProductProjection C i) (AlgHom.id k N) (ρ x) =
      Δ (C x i))
    (x : AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] N))
    (j : J) : C x j = algebraMap k N (v5ProductComponentFixedEquiv C ρ Δ ε hleft he x j) := by
  change C x j = algebraMap k N (ε (C x j))
  exact (v5_product_component_fixed_iff C ρ Δ ε hleft he x).mp x.property j
end StrictEUnit
#print axioms StrictEUnit.v5ProductComponentFixedEquiv_coordinates132
