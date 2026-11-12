import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Ring

/-!
# One denominator for a finite family of rational coordinates

The degree bound and denominator are chosen before all constant linear
combinations. No bound on the constants or nonzero-family premise is needed.
-/

noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- Clear every coordinate once. The SAME degree bound works for all
K-linear combinations and all coordinates, including an empty family. -/
theorem exists_uniform_rational_coordinate_clearing
    {K I J : Type*} [Field K] [Fintype I] [Fintype J]
    (c : I → J → RatFunc K) :
    ∃ D : ℕ, ∃ T : Polynomial K, T ≠ 0 ∧
      ∀ (w : I → K) (j : J), ∃ p : Polynomial K,
        p.natDegree ≤ D ∧
        algebraMap (Polynomial K) (RatFunc K) p =
          algebraMap (Polynomial K) (RatFunc K) T *
            ∑ i, algebraMap K (RatFunc K) (w i) * c i j := by
  classical
  obtain ⟨T, hT⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (Polynomial K)) (fun ij : I × J => c ij.1 ij.2)
  choose N hN using hT
  let D : ℕ := Finset.univ.sup (fun ij : I × J => (N ij).natDegree)
  have hNmap (i : I) (j : J) :
      algebraMap (Polynomial K) (RatFunc K) (N (i,j)) =
        algebraMap (Polynomial K) (RatFunc K) (T : Polynomial K) * c i j := by
    simpa only [Algebra.smul_def] using hN (i,j)
  have hC (x : K) :
      algebraMap (Polynomial K) (RatFunc K) (Polynomial.C x) =
        algebraMap K (RatFunc K) x := by
    simpa only [Polynomial.algebraMap_eq] using
      (IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K) x).symm
  refine ⟨D, (T : Polynomial K),
    mem_nonZeroDivisors_iff_ne_zero.mp T.property, ?_⟩
  intro w j
  refine ⟨∑ i, Polynomial.C (w i) * N (i,j), ?_, ?_⟩
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    exact (Polynomial.natDegree_C_mul_le (w i) (N (i,j))).trans
      (Finset.le_sup (f := fun ij : I × J => (N ij).natDegree)
        (Finset.mem_univ (i,j)))
  · simp only [map_sum, map_mul, hC]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hNmap]
    ring

end StrictEUnit
end
