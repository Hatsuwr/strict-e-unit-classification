import LaurentDerivativeConstants
import DerivativeStableNormalizedGraph
import Stage14LaurentPolynomialODEClosure

/-!
# Constant basis of a derivative-stable Laurent graph

The normalized coordinate chart is explicit. Its entries are NOT assumed
constant: this is derived from stability and the actual Laurent derivative
kernel. Existence of a chart for an arbitrary subspace remains separate.
-/
noncomputable section
namespace StrictEUnit

/-- In an explicit graph chart, derivative invariance produces literal
constant graph entries and a basis whose ambient coordinates all lie in K.
The constant entry is exactly the zeroth Laurent coefficient of that entry. -/
theorem laurent_stable_normalizedGraph_constant_basis
    {K I J : Type*} [Field K] [CharZero K] [Fintype I]
    (B : J → I → LaurentSeries K)
    (hstable : ∀ v : (I → LaurentSeries K) × (J → LaurentSeries K),
      v ∈ LinearMap.range (normalizedGraphMap B) →
      ((fun i => laurentOrdinaryDerivation (v.1 i)),
        (fun j => laurentOrdinaryDerivation (v.2 j))) ∈
        LinearMap.range (normalizedGraphMap B)) :
    (∀ j i, B j i = algebraMap K (LaurentSeries K) ((B j i).coeff 0)) ∧
      ∃ b : Basis I (LaurentSeries K) (LinearMap.range (normalizedGraphMap B)),
        ∀ i, ((b i : LinearMap.range (normalizedGraphMap B)) :
          (I → LaurentSeries K) × (J → LaurentSeries K)) =
          ((fun a => algebraMap K (LaurentSeries K) (((Pi.basisFun K I) i) a)),
            (fun j => algebraMap K (LaurentSeries K) ((B j i).coeff 0))) := by
  classical
  have hz : ∀ j i, laurentOrdinaryDerivation (B j i) = 0 := by
    simpa only [stage14_laurentAlgebraDerivation_apply] using
      (normalizedGraph_derivation_eq_zero (k := K) (F := LaurentSeries K)
        (stage14_laurentAlgebraDerivation (k := K)) B
        (by simpa only [stage14_laurentAlgebraDerivation_apply] using hstable))
  have hB (j : J) (i : I) :
      B j i = algebraMap K (LaurentSeries K) ((B j i).coeff 0) :=
    (laurentOrdinaryDerivation_eq_zero_iff_eq_constant (B j i)).mp (hz j i)
  refine ⟨hB, normalizedGraphBasis B, ?_⟩
  intro i
  rw [normalizedGraphBasis_coe]
  apply Prod.ext
  · funext a
    by_cases ha : a = i <;> simp [Pi.basisFun_apply, ha]
  · funext j
    exact hB j i

end StrictEUnit
end
