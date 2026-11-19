import V5RelativeChartIdeal

noncomputable section
open scoped TensorProduct
open Algebra.TensorProduct
namespace StrictEUnit
variable {B R T J : Type*} {D : J → Type*}
    [CommRing B] [CommRing R] [CommRing T] [∀ j, CommRing (D j)]
    [Algebra B R] [Algebra B T] [Algebra T R] [IsScalarTower B T R]
    [∀ j, Algebra R (D j)] [DecidableEq J]

/-- The left-tensor compatibility in the relative identity chart is forced by
the right-tensor coordinate identity and injectivity of scalar inclusion
in the identity factor. -/
theorem v5_relative_identity_chart_from_right130
    (i : J) (chart : R ⊗[B] R ≃ₐ[R] (∀ j, D j))
    (E : R ⊗[B] T ≃ₐ[R] (J → R))
    (hr : ∀ t j, chart (1 ⊗ₜ[B] algebraMap T R t) j =
      algebraMap R (D j) (E (1 ⊗ₜ[B] t) j))
    (hi : ∀ t, chart (1 ⊗ₜ[B] algebraMap T R t) i =
      algebraMap R (D i) (algebraMap T R t))
    (hinj : Function.Injective (algebraMap R (D i))) :
    ∃ rel : R ⊗[T] R ≃ₐ[R] D i, ∀ a b,
      rel (a ⊗ₜ[T] b) = chart (a ⊗ₜ[B] b) i := by
  apply v5_split_chart_identity_factor i chart E hr
  intro t j
  have hm : E (1 ⊗ₜ[B] t) i = algebraMap T R t :=
    hinj ((hr t i).symm.trans (hi t))
  rw [hm]
  exact congrFun (chart.commutes (algebraMap T R t)) j

omit [IsScalarTower B T R] [DecidableEq J] in
/-- The right-coordinate identity over scalar 1 implies the required
compatibility over every left scalar by R-linearity of the chart. -/
theorem v5_relative_chart_scale_right130
    (chart : R ⊗[B] R ≃ₐ[R] (∀ j, D j))
    (E : R ⊗[B] T ≃ₐ[R] (J → R))
    (hr : ∀ t j, chart (1 ⊗ₜ[B] algebraMap T R t) j =
      algebraMap R (D j) (E (1 ⊗ₜ[B] t) j)) :
    ∀ t (r : R) j, chart (r ⊗ₜ[B] algebraMap T R t) j =
      algebraMap R (D j) (E (r ⊗ₜ[B] t) j) := by
  intro t r j
  have hc : chart (r ⊗ₜ[B] (1 : R)) j = algebraMap R (D j) r :=
    congrFun (chart.commutes r) j
  have he : E (r ⊗ₜ[B] (1 : T)) j = r :=
    congrFun (E.commutes r) j
  rw [show r ⊗ₜ[B] algebraMap T R t =
    (r ⊗ₜ[B] (1 : R)) * (1 ⊗ₜ[B] algebraMap T R t) by simp,
    show r ⊗ₜ[B] t = (r ⊗ₜ[B] (1 : T)) * (1 ⊗ₜ[B] t) by simp,
    map_mul, map_mul, Pi.mul_apply, Pi.mul_apply, hc, he, hr, map_mul]
end StrictEUnit
#print axioms StrictEUnit.v5_relative_identity_chart_from_right130
#print axioms StrictEUnit.v5_relative_chart_scale_right130
