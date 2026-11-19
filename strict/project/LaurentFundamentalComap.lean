import MatrixDualBinomial
import Stage14LaurentPolynomialODEClosure

/-!
Exact differential straightening with the original Laurent derivative.
Only the equation W' = A*W is used for the identity and comap stability.
The matrix products have actual Matrix-typed operands throughout.
-/
noncomputable section
open scoped Matrix
namespace StrictEUnit

/-- Leibniz straightens the original minus-left connection. There is no
inverse differentiation and no linearity of D over the Laurent field. -/
theorem laurent_fundamental_mulVec_dual_eq
    {K : Type*} [Field K] {r : ℕ}
    (A W : Matrix (Fin r) (Fin r) (LaurentSeries K))
    (hW : ∀ i j, laurentOrdinaryDerivation (W i j) = (A*W) i j)
    (x : Fin r → LaurentSeries K) :
    (fun i => laurentOrdinaryDerivation ((W *ᵥ x) i)) - A *ᵥ (W *ᵥ x) =
      W *ᵥ (fun i => laurentOrdinaryDerivation (x i)) := by
  have hWmap : W.map (fun z => stage14_laurentAlgebraDerivation (k := K) z) = A*W := by
    apply Matrix.ext
    intro i j
    simpa only [Matrix.map_apply, stage14_laurentAlgebraDerivation_apply] using hW i j
  have h := matrixColumnDerivative_mulVec (k := K) (B := LaurentSeries K)
    (stage14_laurentAlgebraDerivation (k := K)) W x
  rw [hWmap, ← Matrix.mulVec_mulVec] at h
  have hD : (fun i => laurentOrdinaryDerivation ((W *ᵥ x) i)) =
      A *ᵥ (W *ᵥ x) + W *ᵥ (fun i => laurentOrdinaryDerivation (x i)) := by
    simpa only [matrixColumnDerivative, stage14_laurentAlgebraDerivation_apply] using h
  rw [hD]
  abel

/-- The comap through the SAME W is derivative-invariant whenever E is
invariant under the original connection. Invertibility is not needed here. -/
theorem laurent_fundamental_comap_derivative_stable
    {K : Type*} [Field K] {r : ℕ}
    (A W : Matrix (Fin r) (Fin r) (LaurentSeries K))
    (hW : ∀ i j, laurentOrdinaryDerivation (W i j) = (A*W) i j)
    (E : Submodule (LaurentSeries K) (Fin r → LaurentSeries K))
    (hstable : ∀ v : Fin r → LaurentSeries K, v ∈ E →
      ((fun i => laurentOrdinaryDerivation (v i)) - A *ᵥ v) ∈ E) :
    ∀ x : Fin r → LaurentSeries K, x ∈ E.comap (Matrix.toLin' W) →
      (fun i => laurentOrdinaryDerivation (x i)) ∈ E.comap (Matrix.toLin' W) := by
  intro x hx
  change W *ᵥ (fun i => laurentOrdinaryDerivation (x i)) ∈ E
  have hv : W *ᵥ x ∈ E := hx
  have h := hstable (W *ᵥ x) hv
  rw [laurent_fundamental_mulVec_dual_eq A W hW x] at h
  exact h

end StrictEUnit
end
