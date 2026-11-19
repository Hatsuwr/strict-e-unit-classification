import FiniteRationalCoordinateClearing
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Ratios of constant combinations in a finite-dimensional rational space

The coordinate basis is chosen only from the fixed space; one common
coordinate denominator then gives a bound independent of both combinations.
-/

noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- A fixed finite family in a finite-dimensional K(z)-space has uniformly
bounded rational ratios between its K-linear combinations. -/
theorem exists_uniform_finiteDimensional_rational_ratio_bound
    {K V I : Type*} [Field K] [AddCommGroup V]
    [Module (RatFunc K) V] [FiniteDimensional (RatFunc K) V] [Fintype I]
    (S : I → V) :
    ∃ D : ℕ, ∀ (α β : I → K) (q : RatFunc K),
      (∑ i, algebraMap K (RatFunc K) (β i) • S i) ≠ 0 →
      (∑ i, algebraMap K (RatFunc K) (α i) • S i) =
        q • (∑ i, algebraMap K (RatFunc K) (β i) • S i) →
      ∃ p₁ p₂ : Polynomial K, p₂ ≠ 0 ∧
        p₁.natDegree ≤ D ∧ p₂.natDegree ≤ D ∧
        q = algebraMap (Polynomial K) (RatFunc K) p₁ /
          algebraMap (Polynomial K) (RatFunc K) p₂ := by
  classical
  let e := Module.finBasis (RatFunc K) V
  obtain ⟨D, T, hT, hclear⟩ := exists_uniform_rational_coordinate_clearing
    (fun i j => e.equivFun (S i) j)
  have hrepr (w : I → K) (j : Fin (Module.finrank (RatFunc K) V)) :
      e.equivFun (∑ i, algebraMap K (RatFunc K) (w i) • S i) j =
        ∑ i, algebraMap K (RatFunc K) (w i) * e.equivFun (S i) j := by
    simp only [map_sum, LinearEquiv.map_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
  refine ⟨D, ?_⟩
  intro α β q hb hab
  have hbmap : e.equivFun (∑ i, algebraMap K (RatFunc K) (β i) • S i) ≠ 0 := by
    intro h
    apply hb
    apply e.equivFun.injective
    simpa only [map_zero] using h
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hbmap
  have hj' : (∑ i, algebraMap K (RatFunc K) (β i) * e.equivFun (S i) j) ≠ 0 := by
    simpa only [hrepr, Pi.zero_apply] using hj
  obtain ⟨p₁, hp₁, hmap₁⟩ := hclear α j
  obtain ⟨p₂, hp₂, hmap₂⟩ := hclear β j
  have hp₂map : algebraMap (Polynomial K) (RatFunc K) p₂ ≠ 0 := by
    rw [hmap₂]
    exact mul_ne_zero (RatFunc.algebraMap_ne_zero hT) hj'
  have hp₂ne : p₂ ≠ 0 := by
    intro h
    apply hp₂map
    rw [h, map_zero]
  have hrel := congrArg (fun x : V => e.equivFun x j) hab
  dsimp only at hrel
  simp only [hrepr, LinearEquiv.map_smul, Pi.smul_apply, smul_eq_mul] at hrel
  refine ⟨p₁, p₂, hp₂ne, hp₁, hp₂, ?_⟩
  apply (eq_div_iff hp₂map).mpr
  rw [hmap₁, hmap₂, hrel]
  ring

end StrictEUnit
end
