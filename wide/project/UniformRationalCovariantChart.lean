import OrdinaryPointLaurentFundamental
import OrdinaryPointInvariantChartFactorization
import FiniteSubspaceCoordinateChart
import FixedMatrixRationalChartBound

/-!
One degree bound for normalized rational charts of all invariant subspaces of
one fixed rational connection. The ordinary point, fundamental matrix and
fixed finite-product ratio bound are selected BEFORE the subspace. Returned
polynomials stay in the original RatFunc variable; none is translated back.
-/
noncomputable section
open scoped Matrix
namespace StrictEUnit

/-- A genuine fixed-A uniform chart bound. Only original rational connection
invariance is supplied for E. Its chart, basis, constant realization and
nonzero pivot determinant are derived, not new premises. -/
theorem exists_uniform_rational_covariant_chart_bound
    {K : Type*} [Field K] [CharZero K] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (RatFunc K)) :
    ∃ D : ℕ, ∀ E : Submodule (RatFunc K) (Fin r → RatFunc K),
      (∀ v : Fin r → RatFunc K, v ∈ E →
        ((fun i => stage14_rationalOrdinaryDerivation (v i)) - A *ᵥ v) ∈ E) →
      ∃ s : ℕ, s ≤ r ∧ s = Module.finrank (RatFunc K) E ∧
        ∃ p : Fin s ↪ Fin r, ∃ b : Basis (Fin s) (RatFunc K) E,
          (∀ i j : Fin s, (b j : Fin r → RatFunc K) (p i) =
            if i = j then 1 else 0) ∧
          Submodule.span (RatFunc K)
            (Set.range (fun j : Fin s => (b j : Fin r → RatFunc K))) = E ∧
          (∀ i : Fin r, ∀ j : Fin s, ∃ p₁ p₂ : Polynomial K, p₂ ≠ 0 ∧
            p₁.natDegree ≤ D ∧ p₂.natDegree ≤ D ∧
            (b j : Fin r → RatFunc K) i =
              algebraMap (Polynomial K) (RatFunc K) p₁ /
                algebraMap (Polynomial K) (RatFunc K) p₂) := by
  classical
  obtain ⟨β, W, hunit, hW⟩ := exists_ordinaryPoint_laurent_fundamentalMatrix A
  obtain ⟨D, hD⟩ := exists_uniform_fixedMatrix_rational_chart_bound
    (ordinaryPointRationalAlgHom β) W
  refine ⟨D, ?_⟩
  intro E hstable
  obtain ⟨s, hs, hdim, p, e, b, he, hbe, hpivot, hspan⟩ :=
    exists_normalized_subspace_coordinate_basis E
  let B : Matrix (Fin r) (Fin s) (RatFunc K) :=
    Matrix.of (fun i j => (b j : Fin r → RatFunc K) i)
  obtain ⟨C, hfactor, hdet⟩ := ordinaryPoint_invariant_chart_fundamental_factorization
    β A W hunit hW E b p hpivot hstable
  refine ⟨s, hs, hdim, p, b, hpivot, hspan, ?_⟩
  intro i j
  exact hD s hs C p B hdet hfactor i j

end StrictEUnit
end
