import DifferentialBasisRangeBaseChange
import OrdinaryPointRationalEmbedding

/-!
Actual ordinary-point scalar extension of an invariant rational subspace.
The basis is the SAME supplied actual basis of E, so a normalized coordinate
basis from FiniteSubspaceCoordinateChart can be used without selecting another.
The actual differential compatibility is proved by the accepted translated
rational embedding, not added as a premise here.
-/
noncomputable section
open scoped Matrix
namespace StrictEUnit

/-- The actual Laurent range of the mapped original rational basis is stable
under the actual ordinary Laurent derivative minus the mapped original A.
Normalization is unnecessary for this differential statement. It does not
assert a dimension, pivot factorization, rational descent or rank estimate. -/
theorem ordinaryPoint_basis_range_covariant_stable
    {K : Type*} [Field K] {r s : ℕ} (β : K)
    (A : Matrix (Fin r) (Fin r) (RatFunc K))
    (E : Submodule (RatFunc K) (Fin r → RatFunc K))
    (b : Basis (Fin s) (RatFunc K) E)
    (hstable : ∀ v : Fin r → RatFunc K, v ∈ E →
      ((fun i => stage14_rationalOrdinaryDerivation (v i)) - A *ᵥ v) ∈ E) :
    let B : Matrix (Fin r) (Fin s) (RatFunc K) :=
      Matrix.of (fun j i => (b i : Fin r → RatFunc K) j)
    let φ := (ordinaryPointRationalAlgHom β).toRingHom
    ∀ v : Fin r → LaurentSeries K, v ∈ LinearMap.range ((B.map φ).mulVecLin) →
      ((fun i => laurentOrdinaryDerivation (v i)) - A.map φ *ᵥ v) ∈
        LinearMap.range ((B.map φ).mulVecLin) := by
  have hφ : ∀ z : RatFunc K,
      stage14_laurentAlgebraDerivation (k := K)
        ((ordinaryPointRationalAlgHom β).toRingHom z) =
      (ordinaryPointRationalAlgHom β).toRingHom
        (stage14_rationalOrdinaryDerivation z) := by
    intro z
    simpa only [stage14_laurentAlgebraDerivation_apply] using
      ordinaryPointRationalMap_derivative β z
  have h := differential_map_basis_range_stable (k := K)
    (F := RatFunc K) (L := LaurentSeries K)
    stage14_rationalOrdinaryDerivation (stage14_laurentAlgebraDerivation (k := K))
    (ordinaryPointRationalAlgHom β).toRingHom hφ A E b hstable
  simpa only [stage14_laurentAlgebraDerivation_apply] using h

end StrictEUnit
end
