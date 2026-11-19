import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.Ring

/-!
# Derivative-stable graphs in a fixed coordinate chart

The pivot coordinates are literally the identity. Stability then forces
every graph coefficient into the derivative kernel. No chart existence for
an arbitrary subspace and no coefficient-field linearity of the derivative
is asserted here.
-/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- The literal graph x ↦ (x,Bx), with I as its pivot coordinates. -/
def normalizedGraphMap
    {F I J : Type*} [Field F] [Fintype I] (B : J → I → F) :
    (I → F) →ₗ[F] ((I → F) × (J → F)) where
  toFun x := (x, fun j => ∑ i, B j i * x i)
  map_add' x y := by
    apply Prod.ext
    · rfl
    · funext j
      change (∑ i, B j i * (x i + y i)) =
        (∑ i, B j i * x i) + ∑ i, B j i * y i
      simp only [mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    apply Prod.ext
    · rfl
    · funext j
      change (∑ i, B j i * (a * x i)) = a * ∑ i, B j i * x i
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem normalizedGraphMap_injective
    {F I J : Type*} [Field F] [Fintype I] (B : J → I → F) :
    Function.Injective (normalizedGraphMap B) := by
  intro x y h
  exact congrArg Prod.fst h

/-- The graph columns have identity pivot part and literal B entries. -/
theorem normalizedGraphMap_basisFun
    {F I J : Type*} [Field F] [Fintype I] (B : J → I → F) (i : I) :
    normalizedGraphMap B ((Pi.basisFun F I) i) =
      ((Pi.basisFun F I) i, fun j => B j i) := by
  classical
  apply Prod.ext
  · rfl
  · funext j
    change (∑ a, B j a * ((Pi.basisFun F I) i) a) = B j i
    simp [Pi.basisFun_apply, Pi.single_apply]

/-- A concrete basis of the literal graph range, with no stability assumption. -/
def normalizedGraphBasis
    {F I J : Type*} [Field F] [Fintype I] (B : J → I → F) :
    Basis I F (LinearMap.range (normalizedGraphMap B)) :=
  (Pi.basisFun F I).map
    (LinearEquiv.ofInjective (normalizedGraphMap B) (normalizedGraphMap_injective B))

theorem normalizedGraphBasis_coe
    {F I J : Type*} [Field F] [Fintype I] (B : J → I → F) (i : I) :
    ((normalizedGraphBasis B i : LinearMap.range (normalizedGraphMap B)) :
      (I → F) × (J → F)) = ((Pi.basisFun F I) i, fun j => B j i) := by
  rw [normalizedGraphBasis, Basis.map_apply, LinearEquiv.ofInjective_apply,
    normalizedGraphMap_basisFun]

/-- Stability under the genuine coordinate derivative forces every graph
entry to have zero derivative: a derivative graph column has zero pivots. -/
theorem normalizedGraph_derivation_eq_zero
    {k F I J : Type*} [CommRing k] [Field F] [Algebra k F] [Fintype I]
    (d : Derivation k F F) (B : J → I → F)
    (hstable : ∀ v : (I → F) × (J → F),
      v ∈ LinearMap.range (normalizedGraphMap B) →
      ((fun i => d (v.1 i)), (fun j => d (v.2 j))) ∈
        LinearMap.range (normalizedGraphMap B)) :
    ∀ j i, d (B j i) = 0 := by
  classical
  intro j i
  have he := normalizedGraphMap_basisFun B i
  obtain ⟨x, hx⟩ := (LinearMap.mem_range).mp
    (hstable (normalizedGraphMap B ((Pi.basisFun F I) i))
      (LinearMap.mem_range_self (normalizedGraphMap B) ((Pi.basisFun F I) i)))
  rw [he] at hx
  have hxzero : x = 0 := by
    funext a
    have h := congrArg (fun v : (I → F) × (J → F) => v.1 a) hx
    change x a = d (((Pi.basisFun F I) i) a) at h
    have hd : d (((Pi.basisFun F I) i) a) = 0 := by
      by_cases ha : a = i <;> simp [Pi.basisFun_apply, ha]
    simpa only [hd, Pi.zero_apply] using h
  have h := congrArg (fun v : (I → F) × (J → F) => v.2 j) hx
  change (∑ a, B j a * x a) = d (B j i) at h
  rw [hxzero] at h
  simpa only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] using h.symm

end StrictEUnit
end
