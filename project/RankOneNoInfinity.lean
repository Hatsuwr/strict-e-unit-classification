import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.Algebra.Basic

/-! Vanishing scalar 2-by-2 minors imply an outer product, including the zero
matrix. A decomposable coefficient matrix cannot give a zero product relation
between two independent finite families in a domain unless it is zero. -/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- Explicit pivot decomposition; no finite-index or nonzero-matrix hypothesis. -/
theorem matrix_outerProduct_of_minors_zero
    {k I J : Type*} [Field k] (Z : Matrix I J k)
    (hmin : ∀ i i' j j', Z i j * Z i' j' = Z i j' * Z i' j) :
    ∃ α : I → k, ∃ β : J → k, ∀ i j, Z i j = α i * β j := by
  classical
  by_cases hz : ∀ i j, Z i j = 0
  · exact ⟨fun _ => 0, fun _ => 0, fun i j => by rw [hz i j, zero_mul]⟩
  · obtain ⟨i₀, hi₀⟩ := not_forall.mp hz
    obtain ⟨j₀, hp⟩ := not_forall.mp hi₀
    refine ⟨fun i => Z i j₀ / Z i₀ j₀, fun j => Z i₀ j, ?_⟩
    intro i j
    rw [div_mul_eq_mul_div]
    exact (eq_div_iff hp).mpr (hmin i i₀ j j₀)

/-- A finite independent family's zero linear combination has zero coefficients. -/
theorem independent_finite_sum_eq_zero
    {k A I : Type*} [Field k] [AddCommGroup A] [Module k A] [Fintype I]
    (a : I → A) (ha : LinearIndependent k a) (α : I → k)
    (h : ∑ i, α i • a i = 0) : ∀ i, α i = 0 := by
  classical
  intro i
  exact (linearIndependent_iff'.mp ha) Finset.univ α (by simpa using h) i (Finset.mem_univ i)

/-- The scalar no-infinity lemma. Neither finite type nor algebraic
closedness is required; the two families need not span the ambient algebra. -/
theorem rankOne_product_relation_zero
    {k A I J : Type*} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Fintype I] [Fintype J]
    (a : I → A) (b : J → A) (ha : LinearIndependent k a) (hb : LinearIndependent k b)
    (Z : Matrix I J k)
    (hmin : ∀ i i' j j', Z i j * Z i' j' = Z i j' * Z i' j)
    (hrel : ∑ i, ∑ j, Z i j • (a i * b j) = 0) : Z = 0 := by
  classical
  obtain ⟨α, β, hZ⟩ := matrix_outerProduct_of_minors_zero Z hmin
  have hprod : (∑ i, α i • a i) * (∑ j, β j • b j) = 0 := by
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum, smul_mul_smul_comm]
    simpa only [← hZ] using hrel
  rcases mul_eq_zero.mp hprod with hα | hβ
  · have hα0 := independent_finite_sum_eq_zero a ha α hα
    ext i j
    simp only [hZ, hα0, zero_mul, Matrix.zero_apply]
  · have hβ0 := independent_finite_sum_eq_zero b hb β hβ
    ext i j
    simp only [hZ, hβ0, mul_zero, Matrix.zero_apply]

end StrictEUnit
#print axioms StrictEUnit.matrix_outerProduct_of_minors_zero
#print axioms StrictEUnit.independent_finite_sum_eq_zero
#print axioms StrictEUnit.rankOne_product_relation_zero
