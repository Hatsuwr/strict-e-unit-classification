import V5RelativeIdentityChart130
import V5RelativeFaithfullyFlat

noncomputable section
open scoped TensorProduct
namespace StrictEUnit

/-- The same right-coordinate identity used for the relative tensor square
also proves faithful flatness over T. No second coordinate computation is
needed once the original split charts are available. -/
theorem v5_relative_flat_from_right130
    {k B R T J N : Type*} [Field k]
    [CommRing B] [CommRing R] [CommRing T] [CommRing N] [Nontrivial N]
    [Algebra k B] [Algebra k R] [Algebra k T] [Algebra k N]
    [Algebra B R] [Algebra B T] [Algebra T R]
    [IsScalarTower k B R] [IsScalarTower k B T] [IsScalarTower B T R]
    [Fintype J] [DecidableEq J] [Module.FaithfullyFlat B R]
    (chart : R ⊗[B] R ≃ₐ[R] (J → R ⊗[k] N))
    (E : R ⊗[B] T ≃ₐ[R] (J → R))
    (hr : ∀ t j, chart (1 ⊗ₜ[B] algebraMap T R t) j =
      E (1 ⊗ₜ[B] t) j ⊗ₜ[k] (1 : N)) :
    Module.FaithfullyFlat T R := by
  let E' : T ⊗[B] R ≃ₐ[k] (J → R) :=
    ((Algebra.TensorProduct.comm B T R).trans (E.restrictScalars B)).restrictScalars k
  apply v5_relative_faithfullyFlat_of_component_chart E' chart.toRingEquiv
  intro t r j
  have h := v5_relative_chart_scale_right130 chart E hr t r j
  exact h

end StrictEUnit
#print axioms StrictEUnit.v5_relative_flat_from_right130
