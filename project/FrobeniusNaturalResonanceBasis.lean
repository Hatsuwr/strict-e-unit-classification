import FrobeniusNaturalResonanceIndependence
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# A proved basis of the full nonnegative-power formal solution space

The constructed family's cardinality equals the resonance cost. Its checked
independence and the independently proved upper dimension bound imply equality
of dimension and spanning. The empty resonance set is included. The ambient
space is still defined by the full equation, never by this family's span.
-/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem polynomialLogFormalSolutionSpace_finrank_eq_resonanceCost
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0 ≠ 0) :
    Module.finrank K (polynomialLogFormalSolutionSpace
      (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i))) ξ) =
      polynomialResonanceTotalCost ξ
        (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0) := by
  letI := polynomialLogFormalSolutionSpace_finiteDimensional _ ξ hP
  apply Nat.le_antisymm (polynomialLogFormalSolutionSpace_finrank_le_resonanceCost _ ξ hP)
  simpa only [polynomialLogResonanceCoordinateIndex_card] using
    (naturalResonanceFrobeniusSolution_linearIndependent r b ξ hP).fintype_card_le_finrank

/-- Completeness follows from the matching cardinality, not a supplied
spanning premise. It remains valid when the resonance index is empty. -/
theorem naturalResonanceFrobeniusSolution_span_eq_top
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0 ≠ 0) :
    Submodule.span K (Set.range (naturalResonanceFrobeniusSolution r b ξ hP)) = ⊤ := by
  letI := polynomialLogFormalSolutionSpace_finiteDimensional _ ξ hP
  apply (naturalResonanceFrobeniusSolution_linearIndependent r b ξ hP).span_eq_top_of_card_eq_finrank'
  rw [polynomialLogResonanceCoordinateIndex_card,
    polynomialLogFormalSolutionSpace_finrank_eq_resonanceCost r b ξ hP]

def naturalResonanceFrobeniusBasis
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0 ≠ 0) :
    Basis (polynomialLogResonanceCoordinateIndex ξ
      (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0)) K
      (polynomialLogFormalSolutionSpace
        (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i))) ξ) :=
  Basis.mk (naturalResonanceFrobeniusSolution_linearIndependent r b ξ hP)
    (naturalResonanceFrobeniusSolution_span_eq_top r b ξ hP).ge

/-- The basis vectors are exactly the already constructed coefficient solutions. -/
theorem naturalResonanceFrobeniusBasis_apply
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0 ≠ 0)
    (i : polynomialLogResonanceCoordinateIndex ξ
      (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0)) :
    naturalResonanceFrobeniusBasis r b ξ hP i = naturalResonanceFrobeniusSolution r b ξ hP i :=
  Basis.mk_apply _ _ i

/-- Every actual coefficient solution has a UNIQUE expansion in the exact
constructed shifted family. This is a full coefficient-space spanning theorem. -/
theorem polynomialLogFormalSolution_existsUnique_expansion
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0 ≠ 0)
    (u : ℕ → Polynomial K)
    (hu : ∀ m,polynomialLogEulerCoefficient
      (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i))) ξ u m = 0) :
    ∃! c : polynomialLogResonanceCoordinateIndex ξ
        (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0) → K,
      u = ∑ i,c i • naturalResonanceFrobeniusCoefficients
        (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i))) ξ i := by
  let v : polynomialLogFormalSolutionSpace
      (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i))) ξ := ⟨u,hu⟩
  let basis := naturalResonanceFrobeniusBasis r b ξ hP
  have h := basis.sum_repr v
  have hc := congrArg (polynomialLogFormalSolutionSpace
    (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i))) ξ).subtype h
  simp only [map_sum,map_smul,basis,naturalResonanceFrobeniusBasis_apply] at hc
  refine ⟨fun i => basis.repr v i,hc.symm,?_⟩
  intro d hd
  apply funext
  apply (Fintype.linearIndependent_iffₛ.mp
    (naturalResonanceFrobeniusCoefficients_linearIndependent _ ξ))
  exact hd.symm.trans hc.symm

end StrictEUnit
end

#print axioms StrictEUnit.polynomialLogFormalSolutionSpace_finrank_eq_resonanceCost
#print axioms StrictEUnit.naturalResonanceFrobeniusSolution_span_eq_top
#print axioms StrictEUnit.naturalResonanceFrobeniusBasis_apply
#print axioms StrictEUnit.polynomialLogFormalSolution_existsUnique_expansion
