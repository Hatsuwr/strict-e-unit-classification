import FiniteSubspaceCoordinateChart
import CoordinateChartFullGraph
import LaurentStableGraphDescent

/-!
Constant Laurent-field bases of arbitrary derivative-invariant subspaces.
Only invariance under the actual Laurent ordinary derivative is assumed.
The coordinate chart, normalized basis and graph stability are all derived.
-/
noncomputable section
namespace StrictEUnit

/-- Every subspace of a finite Laurent coordinate space preserved by the
actual ordinary derivative has a Laurent-field basis of literal constant
vectors. The constants are their original zeroth Laurent coefficients.
The number of vectors is the actual dimension, including the zero subspace. -/
theorem laurent_stable_subspace_constant_basis
    {K : Type*} [Field K] [CharZero K] {r : ℕ}
    (E : Submodule (LaurentSeries K) (Fin r → LaurentSeries K))
    (hstable : ∀ v : Fin r → LaurentSeries K, v ∈ E →
      (fun j => laurentOrdinaryDerivation (v j)) ∈ E) :
    ∃ s : ℕ, s ≤ r ∧ s = Module.finrank (LaurentSeries K) E ∧
      ∃ p : Fin s ↪ Fin r, ∃ b : Basis (Fin s) (LaurentSeries K) E,
        (∀ i : Fin s, ∀ j : Fin r,
          (b i : Fin r → LaurentSeries K) j =
            algebraMap K (LaurentSeries K)
              (((b i : Fin r → LaurentSeries K) j).coeff 0)) ∧
        (∀ i j : Fin s,
          (b j : Fin r → LaurentSeries K) (p i) = if i = j then 1 else 0) ∧
        Submodule.span (LaurentSeries K)
          (Set.range (fun j : Fin s => (b j : Fin r → LaurentSeries K))) = E := by
  classical
  obtain ⟨s, hs, hdim, p, e, b, he, hbe, hpivot, hspan⟩ :=
    exists_normalized_subspace_coordinate_basis E
  let B : Fin r → Fin s → LaurentSeries K :=
    fun j i => (b i : Fin r → LaurentSeries K) j
  have hgraph := coordinateChart_fullGraph_stable (k := K) (F := LaurentSeries K)
    (stage14_laurentAlgebraDerivation (k := K)) E p e b he hbe
    (by simpa only [stage14_laurentAlgebraDerivation_apply] using hstable)
  have hconstant := (laurent_stable_normalizedGraph_constant_basis B
    (by simpa only [stage14_laurentAlgebraDerivation_apply] using hgraph)).1
  refine ⟨s, hs, hdim, p, b, ?_, hpivot, hspan⟩
  intro i j
  exact hconstant j i

end StrictEUnit
end
