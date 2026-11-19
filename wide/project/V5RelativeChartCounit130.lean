import V5RelativeIdentityChart130

noncomputable section
open scoped TensorProduct
namespace StrictEUnit

/-- A pointed coefficient algebra makes the left scalar inclusion in
its tensor extension injective, without separate nontriviality search. -/
theorem v5_tensor_left_scalar_injective_of_point130
    {k R N : Type*} [Field k] [CommRing R] [CommRing N] [Algebra k R] [Algebra k N]
    (p : N →ₐ[k] k) : Function.Injective (algebraMap R (R ⊗[k] N)) := by
  let ev := (Algebra.TensorProduct.rid k R R).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id R R) p)
  have hp : Function.LeftInverse ev (algebraMap R (R ⊗[k] N)) := by
    intro r
    exact ev.commutes r
  exact hp.injective

theorem v5_relative_identity_tensor_chart130
    {k B R T J N : Type*} [Field k]
    [CommRing B] [CommRing R] [CommRing T] [CommRing N]
    [Algebra k R] [Algebra k N] [Algebra B R] [Algebra B T]
    [Algebra T R] [IsScalarTower B T R] [DecidableEq J]
    (p : N →ₐ[k] k) (i : J)
    (chart : R ⊗[B] R ≃ₐ[R] (J → R ⊗[k] N))
    (E : R ⊗[B] T ≃ₐ[R] (J → R))
    (hr : ∀ t j, chart (1 ⊗ₜ[B] algebraMap T R t) j =
      E (1 ⊗ₜ[B] t) j ⊗ₜ[k] (1 : N))
    (hi : ∀ t, chart (1 ⊗ₜ[B] algebraMap T R t) i =
      (algebraMap T R t) ⊗ₜ[k] (1 : N)) :
    ∃ rel : R ⊗[T] R ≃ₐ[R] R ⊗[k] N, ∀ a b,
      rel (a ⊗ₜ[T] b) = chart (a ⊗ₜ[B] b) i :=
  v5_relative_identity_chart_from_right130 i chart E hr hi
    (v5_tensor_left_scalar_injective_of_point130 p)

end StrictEUnit
#print axioms StrictEUnit.v5_tensor_left_scalar_injective_of_point130
#print axioms StrictEUnit.v5_relative_identity_tensor_chart130
